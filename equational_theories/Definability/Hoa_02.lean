import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(X,X) = X then m(X,Y) else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxx_x_pyx_pxy_pyy_Equation418 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a a = a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq64 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq64 X0
       grind)
    | exact resolve eq13 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq378 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq393 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq379 X0 (τ X1)
       grind)
    | exact superpose eq379 eq19
    | (have j1 := eq379 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq396 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq379 (σ X0) (σ X1)
       grind)
    | exact superpose eq379 eq15
    | (have j1 := eq379 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq454 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq393 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq393
    | exact resolve eq393 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq488 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq454 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq454
    | (have j0 := eq454 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq454 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq622 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq396 x y
       grind)
    | exact superpose eq396 eq16
    | (have j1 := eq396 x y
       grind)
    | exact resolve eq16 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq635 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq622
       have i₂ := eq488 y x
       grind)
    | exact superpose eq488 eq622
    | (have j1 := eq488 (σ x) (σ y)
       grind)
    | (have r₁ := eq622
       have r₂ := eq488 y x
       grind)
    | (have r₁ := eq622
       have r₂ := eq488 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq622
       have r₂ := eq488 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq622 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488 eq622
  have eq636 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq635
  have eq638 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq636
       grind)
    | exact superpose eq636 eq16
    | exact resolve eq16 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq639 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq638
       have i₂ := eq64 (σ x)
       grind)
    | exact superpose eq64 eq638
    | exact resolve eq638 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq640 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq639
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq639
    | exact resolve eq639 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq641 : (σ x) = (σ y) := by grind
  clear eq640
  have eq654 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq641
       grind)
    | exact superpose eq641 eq16
    | exact resolve eq16 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq655 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq641
       grind)
    | exact superpose eq641 eq10
    | exact resolve eq10 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq692 : x = y := by
    first
    | (have i₁ := eq655
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq655
    | exact resolve eq655 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq693 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq654
       have i₂ := eq64 (σ x)
       grind)
    | exact superpose eq64 eq654
    | exact resolve eq654 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq694 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq693
       have i₂ := eq692
       grind)
    | exact superpose eq692 eq693
    | exact resolve eq693 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692 eq693
  have eq695 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq694
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq694
    | exact resolve eq694 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq694
  have eq696 : False := by grind
  exact eq696

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxy_y_pxy_y_pxy_Equation419 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ b ∨ k a b = b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq74 : y ≠ (M.op x y) ∨ (M.op x x) = (M.op y y) ∨ y = (k x y) := by
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
  have eq75 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq82 x y
       grind)
    | exact superpose eq82 eq44
    | (have j1 := eq82 x y
       grind)
    | exact resolve eq44 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq124 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq121
    | exact resolve eq121 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq192 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq125 eq82
    | (have j0 := eq82 (σ x) (σ y)
       grind)
    | exact resolve eq82 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq192
    | exact resolve eq192 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq196 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq193
       have r₂ := eq27
       grind)
    | exact resolve eq193 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq198 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq196
    | exact resolve eq196 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq200 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq198 eq27
    | exact resolve eq27 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq198 eq75
    | (have r₁ := eq75
       have r₂ := eq198
       grind)
    | exact resolve eq75 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq198
  have eq358 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq357
  have eq365 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq358 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq358
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq358
       grind)
    | exact resolve eq13 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq438 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq365 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq441 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq438
    | exact resolve eq438 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq445 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq125 eq441
    | exact resolve eq441 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq441
  have eq453 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq445
  have eq456 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq453
       have r₂ := eq200
       grind)
    | exact resolve eq453 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq453
  have eq457 : y = (M.op x y) := by
    first
    | (have r₁ := eq456
       have r₂ := eq27
       grind)
    | exact resolve eq456 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq458 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq457 eq20
    | exact resolve eq20 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq461 : y ≠ y ∨ (M.op x x) = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq457 eq74
    | (have r₁ := eq74
       have r₂ := eq457
       grind)
    | exact resolve eq74 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq466 : (M.op x x) = (M.op y y) ∨ y = (k x y) := by grind
  clear eq461
  have eq473 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq458
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq458
    | exact resolve eq458 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq477 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq473 eq26
    | exact resolve eq26 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq743 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k X0 y) = (M.op X0 y) ∨ y = (k x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq466
       grind)
    | exact superpose eq466 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq466
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq466
       grind)
    | exact resolve eq13 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq813 : (M.op x y) = (k x y) ∨ y = (k x y) := by
    first
    | (have j0 := eq743 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq818 : (M.op x y) = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq813
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq813
    | exact resolve eq813 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq813
  have eq821 : y = (k x y) ∨ y = (k x y) := by
    first
    | exact superpose eq457 eq818
    | exact resolve eq818 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457 eq818
  have eq822 : y = (k x y) := by grind
  clear eq821
  have eq826 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq822
       grind)
    | exact superpose eq822 eq44
    | exact resolve eq44 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq822
  have eq833 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq473 eq826
    | exact resolve eq826 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq835 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq833
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq833
    | exact resolve eq833 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq833
  have eq836 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq473 eq835
    | exact resolve eq835 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473 eq835
  have eq839 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq836 eq82
    | (have j0 := eq82 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq82 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq836
  have eq840 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq839
  have eq842 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq477 eq840
    | exact resolve eq840 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477 eq840
  have eq845 : False := by grind
  exact eq845

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation419 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law419 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq116 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq118 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq638 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq118 X0 X1
       grind)
    | exact superpose eq118 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq118 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) X0
       have r₂ := eq118 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq118 (M.op (τ X1) X0) X1
       grind)
    | exact resolve eq13 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq642 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq638 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq643 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq642 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq744 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq116 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq2136 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq643 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq643
    | exact resolve eq643 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq2178 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2136 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2136
    | (have j0 := eq2136 X0 X1
       grind)
    | exact resolve eq2136 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2136
  have eq2214 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq2178 X1 X0
       grind)
    | exact superpose eq2178 eq10
    | (have j1 := eq2178 X1 X0
       grind)
    | exact resolve eq10 eq2178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2255 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2214 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2214
    | (have j0 := eq2214 X0 X1
       grind)
    | exact resolve eq2214 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2214
  have eq2294 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq2255 X0 (σ X1)
       grind)
    | exact superpose eq2255 eq37
    | (have j1 := eq2255 X0 (σ X1)
       grind)
    | exact resolve eq37 eq2255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2255
  have eq3990 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) X0
       have i₂ := eq2294 (σ X0) X1
       grind)
    | exact superpose eq2294 eq28
    | (have j1 := eq2294 (σ X0) X1
       grind)
    | exact resolve eq28 eq2294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2294
  have eq4051 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3990 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3990
    | (have j0 := eq3990 X0 X1
       grind)
    | exact resolve eq3990 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3990
  have eq4085 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4051 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4051
    | (have j0 := eq4051 X0 X1
       grind)
    | exact resolve eq4051 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4051
  have eq4095 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4085 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4085
    | (have j0 := eq4085 X0 X1
       grind)
    | exact resolve eq4085 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4085
  have eq4294 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq4095 X1 X0
       grind)
    | exact superpose eq4095 eq11
    | (have j1 := eq4095 X1 X0
       grind)
    | exact resolve eq11 eq4095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4095
  have eq5156 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4294 y x
       grind)
    | exact superpose eq4294 eq16
    | (have j1 := eq4294 y x
       grind)
    | exact resolve eq16 eq4294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4294
  have eq5186 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5156
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq5156
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq5156
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5156
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5156 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5187 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq5156
       have i₂ := eq2178 y x
       grind)
    | exact superpose eq2178 eq5156
    | (have j1 := eq2178 y x
       grind)
    | (have r₁ := eq5156
       have r₂ := eq2178 y x
       grind)
    | (have r₁ := eq5156
       have r₂ := eq2178 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5156
       have r₂ := eq2178 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5156 eq2178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2178 eq5156
  have eq5190 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5187
  have eq5191 : x = y ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq5190
  have eq5192 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5186
  have eq5193 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq5192
  have eq5197 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5191
       grind)
    | exact superpose eq5191 eq16
    | exact resolve eq16 eq5191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5191
  have eq5198 : x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5197
       have r₂ := eq22 x
       grind)
    | exact resolve eq5197 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5197
  have eq5204 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq744 x y
       have i₂ := eq5198
       grind)
    | exact superpose eq5198 eq744
    | (have j0 := eq744 x y
       grind)
    | exact resolve eq744 eq5198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744 eq5198
  have eq5209 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5204
  have eq5210 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5209
  have eq5214 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5193
       grind)
    | exact superpose eq5193 eq16
    | exact resolve eq16 eq5193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5193
  have eq5215 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5214
       have r₂ := eq22 x
       grind)
    | exact resolve eq5214 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5214
  have eq5227 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5210
       grind)
    | exact superpose eq5210 eq16
    | exact resolve eq16 eq5210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5210
  have eq5257 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5227
       have i₂ := eq5215
       grind)
    | exact superpose eq5215 eq5227
    | exact resolve eq5227 eq5215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5215 eq5227
  have eq5258 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq5257
  have eq5259 : (σ x) = (σ y) := by grind
  clear eq5258
  have eq5260 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5259
       grind)
    | exact superpose eq5259 eq16
    | exact resolve eq16 eq5259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5261 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5259
       grind)
    | exact superpose eq5259 eq10
    | exact resolve eq10 eq5259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5259
  have eq5312 : x = y := by
    first
    | (have i₁ := eq5261
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5261
    | exact resolve eq5261 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5261
  have eq5313 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5260
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5260
    | exact resolve eq5260 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5260
  have eq5314 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5313
       have i₂ := eq5312
       grind)
    | exact superpose eq5312 eq5313
    | exact resolve eq5313 eq5312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5312 eq5313
  have eq5315 : False := by grind
  exact eq5315

/-- `Equation4424`: `x ◇ (x ◇ y) = (z ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_y_pyx_x_pyx_Equation4424 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4424 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4424.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X1) := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X1) = (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 X2) X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 x X1 X3
       have i₂ := eq14 x X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq14 X2 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ X1 ∨ (M.op X0 (M.op X0 X1)) = (k X1 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 (M.op X2 X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 (M.op (M.op X2 X2) X1) (M.op X2 X2)
       have r₂ := eq14 (M.op X2 X2) X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
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
  have eq77 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq78 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq85 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
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
  have eq90 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq16
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq85
    | (have j0 := eq85 X0 (σ X1)
       grind)
    | exact resolve eq85 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq77
       have i₂ := eq85 y x
       grind)
    | exact superpose eq85 eq77
    | (have j1 := eq85 x x
       grind)
    | exact resolve eq77 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
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
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq173 : (σ (k (k y y) y)) = (k (k (σ y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq40 (k y y)
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq40
    | exact resolve eq40 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq78
  have eq243 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k y (τ X0))
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq266 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq415 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq266
  have eq479 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq55 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55
    | (have j0 := eq55 x y X0
       grind)
    | exact resolve eq55 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq55
    | (have j0 := eq55 X0 (σ y) (σ x)
       grind)
    | exact resolve eq55 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq518 : ∀ X0 : G, (M.op (M.op X0 X0) y) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq479 x
       have i₂ := eq14 x y X0
       grind)
    | exact superpose eq14 eq479
    | (have j1 := eq14 x y X0
       grind)
    | exact resolve eq479 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq538 : ∀ X0 : G, (M.op (M.op X0 X0) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq480 X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq480
    | (have j1 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq480 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq711 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = (M.op (M.op X1 X1) (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 x y X1 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq51
    | (have j0 := eq51 x y X1 X0
       grind)
    | exact resolve eq51 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1022 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq115 eq85
    | (have j0 := eq85 x (σ x)
       grind)
    | exact resolve eq85 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq1023 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq1022
    | exact resolve eq1022 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1026 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1023
       have r₂ := eq27
       grind)
    | exact resolve eq1023 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq1174 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1026 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq1026
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq1026
       grind)
    | exact resolve eq13 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq1179 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq1174
  have eq1183 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1179 eq49
    | exact resolve eq49 eq1179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq1179
  have eq1187 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq1183
    | exact resolve eq1183 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1183
  have eq1196 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq85 x x
       have i₂ := eq1187
       grind)
    | exact superpose eq1187 eq85
    | (have j0 := eq85 x x
       grind)
    | exact resolve eq85 eq1187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1197 : x = (M.op x x) := by grind
  clear eq1196
  have eq1201 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq1197
       grind)
    | exact superpose eq1197 eq14
    | exact resolve eq14 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1205 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 x X0 X1
       have i₂ := eq1197
       grind)
    | exact superpose eq1197 eq52
    | exact resolve eq52 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1209 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq518 x
       have i₂ := eq1197
       grind)
    | exact superpose eq1197 eq518
    | exact resolve eq518 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1210 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq538 x
       have i₂ := eq1197
       grind)
    | exact superpose eq1197 eq538
    | exact resolve eq538 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1211 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq1197
       grind)
    | exact superpose eq1197 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq1197
       grind)
    | exact resolve eq13 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197
  have eq1216 : x = (k x x) := by grind
  clear eq1211
  have eq1221 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1209
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1209
    | exact resolve eq1209 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq1266 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq1216
       grind)
    | exact superpose eq1216 eq43
    | exact resolve eq43 eq1216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq1216
  have eq1270 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1266
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1266
    | exact resolve eq1266 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1266
  have eq1333 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (σ X0)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X1) (σ X0) X2
       have i₂ := eq97 X0 X1
       grind)
    | exact superpose eq97 eq14
    | (have j1 := eq97 X0 X1
       grind)
    | exact resolve eq14 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1340 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq97 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1361 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1270 eq85
    | (have j0 := eq85 x (σ x)
       grind)
    | exact resolve eq85 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq1270
  have eq1362 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1361
  have eq1379 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1362 eq538
    | exact resolve eq538 eq1362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538 eq1362
  have eq1392 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq1379
    | exact resolve eq1379 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1379
  have eq1606 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq1392 eq1210
    | exact resolve eq1210 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210 eq1392
  have eq1635 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = (M.op (M.op X1 X1) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq1221 eq711
    | exact resolve eq711 eq1221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq1636 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op (M.op X1 X1) (M.op x y)) := by
    intro X1
    first
    | (have i₁ := eq1635 x X1
       have i₂ := eq518 x
       grind)
    | exact superpose eq518 eq1635
    | exact resolve eq1635 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq1635
  have eq1637 : ∀ X1 : G, (M.op x y) = (M.op (M.op X1 X1) (M.op x y)) := by
    intro X1
    first
    | exact superpose eq1221 eq1636
    | exact resolve eq1636 eq1221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221 eq1636
  have eq1654 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1637 x
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq1637
    | exact resolve eq1637 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1637
  have eq1768 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) ≠ (M.op X0 (M.op x y)) ∨ (M.op X0 (M.op x y)) = (k (M.op X0 (M.op x y)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | exact superpose eq1654 eq67
    | (have r₁ := eq67 X0 (M.op x y) x
       have r₂ := eq1654 X0
       grind)
    | exact resolve eq67 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq1654
  have eq1779 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (k (M.op X0 (M.op x y)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1768 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1768
  have eq14875 : (σ (M.op (M.op x y) (M.op x y))) ≠ (σ (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq1779 eq1340
    | (have j0 := eq1340 (M.op (M.op x y) (M.op x y))
       grind)
    | exact resolve eq1340 eq1779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779
  have eq14889 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1340 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq1340
    | (have j0 := eq1340 (τ X0)
       grind)
    | exact resolve eq1340 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340
  have eq14904 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by grind
  clear eq14875
  have eq14908 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq14889 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq14889
    | (have j0 := eq14889 X0
       grind)
    | exact resolve eq14889 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14889
  have eq14916 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14908 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq14908
    | (have j0 := eq14908 X0
       grind)
    | exact resolve eq14908 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14908
  have eq31389 : ∀ X0 X1 : G, (M.op (σ X1) (σ (k X0 X1))) = (M.op x (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1333 X0 X1 x
       have i₂ := eq1205 (σ X0) x
       grind)
    | exact superpose eq1205 eq1333
    | (have j0 := eq1333 X0 X1 x
       grind)
    | exact resolve eq1333 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205 eq1333
  have eq31643 : ∀ X0 X1 : G, (σ (k (k X0 X1) X1)) = (M.op x (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq97 (k X0 X1) X1
       have i₂ := eq31389 X0 X1
       grind)
    | exact superpose eq31389 eq97
    | (have j0 := eq97 X0 X1
       have j1 := eq31389 X0 X1
       grind)
    | exact resolve eq97 eq31389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq31389
  have eq31660 : ∀ X0 X1 : G, (σ (k (k X0 X1) X1)) = (M.op x (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq31643 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31643
  have eq105518 : ∀ X0 : G, (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op X0 (M.op X0 (σ (M.op (M.op x y) (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq14904 eq55
    | exact resolve eq55 eq14904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq105553 : (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op x (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq105518 x
       have i₂ := eq1201 x (σ (M.op sF0 sF0))
       grind)
    | exact superpose eq1201 eq105518
    | exact resolve eq105518 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105518
  have eq105593 : (σ (M.op (M.op x y) (M.op x y))) = (M.op x (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq14904 eq105553
    | exact resolve eq105553 eq14904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14904 eq105553
  have eq112010 : ∀ X0 : G, (M.op x (σ y)) = (σ (k (τ (k (σ y) X0)) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq31660 y (τ X0)
       have i₂ := eq243 X0
       grind)
    | exact superpose eq243 eq31660
    | (have j0 := eq31660 X0 (τ X0)
       grind)
    | exact resolve eq31660 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq112370 : ∀ X0 : G, (M.op x (σ y)) = (k (k (σ y) X0) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq112010 X0
       have i₂ := eq34 (k sF3 X0) (τ X0)
       grind)
    | exact superpose eq34 eq112010
    | (have j0 := eq112010 X0
       grind)
    | exact resolve eq112010 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112010
  have eq112632 : ∀ X0 : G, (M.op x (σ y)) = (k (k (σ y) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq112370 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq112370
    | (have j0 := eq112370 X0
       grind)
    | exact resolve eq112370 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112370
  have eq112748 : ∀ X0 : G, (M.op x (σ y)) = (k (k (σ y) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq112632 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq112632
    | (have j0 := eq112632 X0
       grind)
    | exact resolve eq112632 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112632
  have eq112791 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (k (σ y) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | exact superpose eq1606 eq112748
    | (have j0 := eq112748 X0
       grind)
    | exact resolve eq112748 eq1606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112748
  have eq112803 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (k (σ y) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq112791 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq112791
    | (have j0 := eq112791 X0
       grind)
    | exact resolve eq112791 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112791
  have eq932320 : ∀ X0 X1 : G, (M.op x (σ (τ X0))) = (σ (k (τ (k X0 X1)) (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq31660 (τ X0) (τ X1)
       have i₂ := eq415 X1 X0
       grind)
    | exact superpose eq415 eq31660
    | (have j0 := eq31660 X0 (τ X1)
       grind)
    | exact resolve eq31660 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415 eq31660
  have eq932386 : ∀ X0 X1 : G, (M.op x (σ (τ X0))) = (k (k X0 X1) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq932320 X0 X1
       have i₂ := eq34 (k X0 X1) (τ X1)
       grind)
    | exact superpose eq34 eq932320
    | (have j0 := eq932320 X0 X1
       grind)
    | exact resolve eq932320 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq932320
  have eq932715 : ∀ X0 X1 : G, (k (k X0 X1) X1) = (M.op x (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq932386 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq932386
    | (have j0 := eq932386 X0 X1
       grind)
    | exact resolve eq932386 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932386
  have eq933016 : ∀ X0 X1 : G, (M.op x X0) = (k (k X0 X1) X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq932715 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq932715
    | (have j0 := eq932715 X0 X1
       grind)
    | exact resolve eq932715 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932715
  have eq933204 : ∀ X0 X1 : G, (M.op x X0) = (k (k X0 X1) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq933016 X0 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq933016
    | (have j0 := eq933016 X0 X1
       grind)
    | exact resolve eq933016 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933016
  have eq958096 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq173
       have i₂ := eq933204 y y
       grind)
    | exact superpose eq933204 eq173
    | (have j1 := eq933204 x y
       grind)
    | exact resolve eq173 eq933204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173 eq933204
  have eq958453 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq958096
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq958096
    | exact resolve eq958096 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958096
  have eq958493 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq958453
    | exact resolve eq958453 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958453
  have eq958561 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq958493 eq112803
    | (have j0 := eq112803 (σ y)
       grind)
    | exact resolve eq112803 eq958493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112803 eq958493
  have eq958603 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq958561
       have r₂ := eq27
       grind)
    | exact resolve eq958561 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958561
  have eq958790 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq958603 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq958603
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq958603
       grind)
    | exact resolve eq13 eq958603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958603
  have eq958847 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq958790
  have eq960962 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq958847 eq90
    | exact resolve eq90 eq958847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq958847
  have eq961244 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq960962
    | exact resolve eq960962 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq960962
  have eq961249 : y = (M.op y y) := by
    first
    | (have j1 := eq14916 y
       grind)
    | (have r₁ := eq961244
       have r₂ := eq14916 y
       grind)
    | exact resolve eq961244 eq14916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14916 eq961244
  have eq961886 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1201 y y
       have i₂ := eq961249
       grind)
    | exact superpose eq961249 eq1201
    | exact resolve eq1201 eq961249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq961989 : y = (M.op x y) := by
    first
    | (have i₁ := eq961886
       have i₂ := eq961249
       grind)
    | exact superpose eq961249 eq961886
    | exact resolve eq961886 eq961249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961886
  have eq962179 : y = (M.op x y) := by
    first
    | (have i₁ := eq961989
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq961989
    | exact resolve eq961989 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq961989
  have eq962323 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq962179 eq20
    | exact resolve eq20 eq962179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq962560 : (σ (M.op y y)) = (M.op x (σ (M.op y y))) := by
    first
    | exact superpose eq962179 eq105593
    | exact resolve eq105593 eq962179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105593 eq962179
  have eq963015 : (σ y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq962560
       have i₂ := eq961249
       grind)
    | exact superpose eq961249 eq962560
    | exact resolve eq962560 eq961249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961249 eq962560
  have eq963110 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq962323
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq962323
    | exact resolve eq962323 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962323
  have eq963258 : (σ y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq963015
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq963015
    | exact resolve eq963015 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq963015
  have eq963342 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1606 eq963258
    | exact resolve eq963258 eq1606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606 eq963258
  have eq963953 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq963110 eq963342
    | exact resolve eq963342 eq963110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963110 eq963342
  have eq963954 : False := by grind
  exact eq963954

/-- `Equation4441`: `x ◇ (y ◇ x) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_x_pyx_pxy_pyx_Equation4441 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4441 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4441.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X3) := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq53 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X5) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq9 X0 x X4 X5
       have i₂ := eq9 X0 x X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 x x
       have i₂ := eq9 X0 X2 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op (M.op X0 X5) X6) = (M.op (M.op (M.op X0 X1) X2) X4) := by
    intro X0 X1 X2 X4 X5 X6
    first
    | (have i₁ := eq53 X0 (M.op x X0) X4 X5 X6
       have i₂ := eq9 X0 x X1 X2
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X2 (M.op X0 X3)) ∨ (M.op (M.op X0 X3) X2) = (k X2 (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 (M.op X0 X3)
       have i₂ := eq9 X0 X1 X3 (M.op X0 X3)
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op X0 X3)
       grind)
    | (have r₁ := eq12 X2 (M.op X2 X2)
       have r₂ := eq9 X2 X2 X2 (M.op X2 X2)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq293 (σ X0)
       grind)
    | exact superpose eq293 eq15
    | exact resolve eq15 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq293 (τ X0)
       grind)
    | exact superpose eq293 eq18
    | exact resolve eq18 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq303 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq300 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq300
    | exact resolve eq300 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq307 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq296 X0
       have i₂ := eq293 X0
       grind)
    | exact superpose eq293 eq296
    | exact resolve eq296 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq311 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq303 X0
       have i₂ := eq293 X0
       grind)
    | exact superpose eq293 eq303
    | exact resolve eq303 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293 eq303
  have eq317 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X1) X2) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1 X2
       have i₂ := eq307 X0
       grind)
    | exact superpose eq307 eq9
    | exact resolve eq9 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op X1 (σ X0))) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0) X2
       have i₂ := eq307 X0
       grind)
    | exact superpose eq307 eq9
    | exact resolve eq9 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq322 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (M.op (σ X0) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (σ X0) (σ X0) X1 X2 X3
       have i₂ := eq307 X0
       grind)
    | exact superpose eq307 eq53
    | exact resolve eq53 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq311 X0
       grind)
    | exact superpose eq311 eq10
    | exact resolve eq10 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq357 : ∀ X0 X1 X2 : G, (M.op (M.op (τ X0) X1) X2) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X0) (τ X0) X1 X2
       have i₂ := eq339 X0
       grind)
    | exact superpose eq339 eq9
    | exact resolve eq9 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq372 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq372 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq372
    | (have j0 := eq372 (σ X0) (σ X1)
       grind)
    | exact resolve eq372 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (σ X0) X1) X2) = (M.op (M.op (σ (M.op X0 X0)) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq69 (σ X0) (σ X0) X3 X4 X1 X2
       have i₂ := eq307 X0
       grind)
    | exact superpose eq307 eq69
    | exact resolve eq69 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq961 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq373 y x
       grind)
    | exact superpose eq373 eq16
    | (have j1 := eq373 y x
       grind)
    | exact resolve eq16 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq1294 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq291 X0 x X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq1306 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1294 (σ X0)
       have i₂ := eq307 X0
       grind)
    | exact superpose eq307 eq1294
    | exact resolve eq1294 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq1316 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1306 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq1306
    | exact resolve eq1306 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306
  have eq1321 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1316 X0
       have i₂ := eq1294 X0
       grind)
    | exact superpose eq1294 eq1316
    | exact resolve eq1316 eq1294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294 eq1316
  have eq2989 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 (σ X0))) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1321 X0
       have i₂ := eq318 X0 X1 (σ X0)
       grind)
    | exact superpose eq318 eq1321
    | exact resolve eq1321 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq2992 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X1) X2) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1321 X0
       have i₂ := eq322 X0 (σ X0) X1 X2
       grind)
    | exact superpose eq322 eq1321
    | exact resolve eq1321 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3079 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq2992 X0 x x
       have i₂ := eq317 X0 x x
       grind)
    | exact superpose eq317 eq2992
    | exact resolve eq2992 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3129 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op (M.op X0 X1) X2)) = (M.op (M.op (σ X0) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2992 X0 X3 X4
       have i₂ := eq53 X0 X0 X0 X1 X2
       grind)
    | (have i₁ := eq2992 X0 X3 X4
       have i₂ := eq53 X0 X1 X2 X0 X0
       grind)
    | exact superpose eq53 eq2992
    | exact resolve eq2992 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq2992
  have eq3816 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3129 X0 X1 X2 x x
       have i₂ := eq317 X0 x x
       grind)
    | exact superpose eq317 eq3129
    | exact resolve eq3129 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22048 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (τ (M.op (σ X0) (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (M.op X0 X0) X0)
       have i₂ := eq2989 X0 X1
       grind)
    | exact superpose eq2989 eq10
    | exact resolve eq10 eq2989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2989
  have eq26872 : ∀ X0 X1 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (M.op (σ (τ X0)) (M.op X1 (σ (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq357 X0 (τ X0) (τ X0)
       have i₂ := eq22048 (τ X0) X1
       grind)
    | exact superpose eq22048 eq357
    | exact resolve eq357 eq22048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22048
  have eq27048 : ∀ X0 X1 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq26872 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26872
    | exact resolve eq26872 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26872
  have eq43503 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X1 X0))) = (M.op (τ (M.op X0 (M.op X1 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq357 X0 (τ (M.op X0 X0)) X2
       have i₂ := eq27048 X0 X1
       grind)
    | exact superpose eq27048 eq357
    | exact resolve eq357 eq27048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq27048
  have eq44263 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq961
       have i₂ := eq372 y x
       grind)
    | exact superpose eq372 eq961
    | (have j1 := eq372 (σ y) (σ x)
       grind)
    | exact resolve eq961 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq961
  have eq44266 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq44263
  have eq44270 : ∀ X0 X1 : G, (M.op (σ (M.op y y)) X0) = (M.op (σ y) X1) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq322 y X0 (σ x) X1
       have i₂ := eq44266
       grind)
    | exact superpose eq44266 eq322
    | exact resolve eq322 eq44266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq64602 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op (M.op X0 X0) X0)) X1) = (M.op (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq419 (M.op X0 X0) (σ X0) X1 X2 X3
       have i₂ := eq1321 X0
       grind)
    | exact superpose eq1321 eq419
    | exact resolve eq419 eq1321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq1321
  have eq65897 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op (M.op X0 X0) X0)) X1) = (M.op (M.op (M.op (σ X0) (σ (M.op X0 X0))) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64602 X0 X1 X2 X3
       have i₂ := eq3816 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq3816 eq64602
    | exact resolve eq64602 eq3816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3816 eq64602
  have eq65951 : ∀ X0 X1 X3 : G, (M.op (M.op (σ X0) (σ (M.op X0 X0))) X3) = (M.op (σ (M.op (M.op X0 X0) X0)) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq65897 X0 X1 x X3
       have i₂ := eq317 X0 (σ (M.op X0 X0)) x
       grind)
    | exact superpose eq317 eq65897
    | exact resolve eq65897 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65897
  have eq65982 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op (M.op X0 X0) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq65951 X0 X1 x
       have i₂ := eq317 X0 (σ (M.op X0 X0)) x
       grind)
    | exact superpose eq317 eq65951
    | exact resolve eq65951 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317 eq65951
  have eq65996 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op (M.op X0 X0) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq65982 X0 X1
       have i₂ := eq3079 X0
       grind)
    | exact superpose eq3079 eq65982
    | exact resolve eq65982 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3079 eq65982
  have eq119535 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X0))) = (M.op (σ (M.op X0 (M.op X1 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65996 x X1
       have i₂ := eq9 x X1 x x
       grind)
    | exact superpose eq9 eq65996
    | exact resolve eq65996 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65996
  have eq2065406 : ∀ X0 X2 : G, (M.op (σ y) X0) = (M.op (σ y) X2) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0 X2
    first
    | (have i₁ := eq44270 x X2
       have i₂ := eq44270 x X0
       grind)
    | exact superpose eq44270 eq44270
    | exact resolve eq44270 eq44270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44270
  have eq2069338 : ∀ X0 X2 : G, (M.op (σ y) X0) = (M.op (σ y) X2) ∨ y = (M.op y x) := by
    intro X0 X2
    first
    | (have j0 := eq2065406 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2065406
  have eq2074096 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq44266
       have i₂ := eq2069338 (σ x) X0
       grind)
    | (have i₁ := eq44266
       have i₂ := eq2069338 X0 (σ x)
       grind)
    | exact superpose eq2069338 eq44266
    | exact resolve eq44266 eq2069338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44266 eq2069338
  have eq2075691 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq2074096 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2074096
  have eq2078248 : ∀ X1 : G, (τ (σ y)) = (M.op (τ (σ y)) X1) ∨ y = (M.op y x) := by
    intro X1
    first
    | (have i₁ := eq43503 (σ y) X1 x
       have i₂ := eq2075691 (M.op X1 (σ y))
       grind)
    | exact superpose eq2075691 eq43503
    | exact resolve eq43503 eq2075691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43503 eq2075691
  have eq2078849 : ∀ X1 : G, y = (M.op y x) ∨ y = (M.op y X1) := by
    intro X1
    first
    | (have i₁ := eq2078248 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2078248
    | exact resolve eq2078248 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078248
  have eq2080118 : y ≠ y ∨ y = (M.op y x) := by
    first
    | (have j0 := eq2078849 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078849
  have eq2080119 : y = (M.op y x) := by grind
  clear eq2080118
  have eq2080172 : ∀ X0 X1 : G, (M.op y (M.op X0 y)) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 y X0 x X1
       have i₂ := eq2080119
       grind)
    | exact superpose eq2080119 eq9
    | exact resolve eq9 eq2080119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2081082 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) := by
    intro X0 X2
    first
    | (have i₁ := eq2080172 x X2
       have i₂ := eq2080172 x X0
       grind)
    | (have i₁ := eq2080172 X0 x
       have i₂ := eq2080172 X0 (M.op X0 y)
       grind)
    | exact superpose eq2080172 eq2080172
    | exact resolve eq2080172 eq2080172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2080172
  have eq2083897 : ∀ X0 : G, y = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq2081082 x X0
       have i₂ := eq2080119
       grind)
    | exact superpose eq2080119 eq2081082
    | exact resolve eq2081082 eq2080119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2080119 eq2081082
  have eq2088163 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 y X1 X2
       have i₂ := eq2083897 X0
       grind)
    | exact superpose eq2083897 eq9
    | exact resolve eq9 eq2083897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2088173 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 y X1
       have i₂ := eq2083897 X0
       grind)
    | exact superpose eq2083897 eq57
    | exact resolve eq57 eq2083897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq2089057 : ∀ X1 : G, (σ y) = (M.op (σ y) X1) := by
    intro X1
    first
    | (have i₁ := eq119535 y X1 x
       have i₂ := eq2083897 (M.op X1 y)
       grind)
    | exact superpose eq2083897 eq119535
    | exact resolve eq119535 eq2083897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119535 eq2083897
  have eq2162025 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) X2)) = (M.op (σ X0) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3129 X0 X1 X2 x x
       have i₂ := eq2088163 (σ X0) x x
       grind)
    | exact superpose eq2088163 eq3129
    | exact resolve eq3129 eq2088163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3129
  have eq2164950 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq2162025 X0 x x
       have i₂ := eq2088163 X0 x x
       grind)
    | exact superpose eq2088163 eq2162025
    | exact resolve eq2162025 eq2088163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088163 eq2162025
  have eq2167331 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2088173 X0 (σ y)
       have i₂ := eq2089057 X0
       grind)
    | exact superpose eq2089057 eq2088173
    | exact resolve eq2088173 eq2089057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088173 eq2089057
  have eq2174132 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2167331 (σ x)
       grind)
    | exact superpose eq2167331 eq16
    | exact resolve eq16 eq2167331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2167331
  have eq2227828 : False := by grind
  exact eq2227828

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxx_pxy_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
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
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
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
  have eq28 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq28 (σ X0)
       grind)
    | exact superpose eq28 eq15
    | exact resolve eq15 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq28 (τ X0)
       grind)
    | exact superpose eq28 eq17
    | exact resolve eq17 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq31
    | exact resolve eq31 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq33
    | exact resolve eq33 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq42 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
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
  have eq43 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq50 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq64 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (k X1 (τ X0))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq34
    | exact resolve eq34 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op X1 (M.op X2 (σ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq9
    | exact resolve eq9 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq77 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 X1
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq73
    | (have j0 := eq73 X0 X1
       grind)
    | exact resolve eq73 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq77
    | (have j0 := eq77 X0 X1
       grind)
    | exact resolve eq77 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq87 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq10
    | exact resolve eq10 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X2 (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (σ X0) X1 X2
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq19
    | exact resolve eq19 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
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
  have eq153 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (τ X0)
       have i₂ := eq87 X0
       grind)
    | exact superpose eq87 eq20
    | exact resolve eq20 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq162 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79 (k X1 (τ X0)) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq79
    | exact resolve eq79 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq79
    | exact resolve eq79 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq191 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq164 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq164
    | (have j0 := eq164 X0 X1
       grind)
    | exact resolve eq164 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq193 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq162 X0 X1 X2
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq162
    | (have j0 := eq162 X0 X1 X2
       grind)
    | exact resolve eq162 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq198 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq191 X0 X1
       have j1 := eq66 X1 X0
       grind)
    | (have r₁ := eq191 (σ X0) X0
       have r₂ := eq66 X0 (σ X0)
       grind)
    | (have r₁ := eq191 X1 X0
       have r₂ := eq66 X0 X1
       grind)
    | exact resolve eq191 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq191
  have eq200 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq193 X0 X1 X2
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq193
    | (have j0 := eq193 X0 X1 X2
       grind)
    | exact resolve eq193 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq193
  have eq261 : ∀ X0 : G, (τ (τ (M.op X0 X0))) = (M.op (τ (τ (M.op X0 X0))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq153 (τ X0)
       have i₂ := eq87 X0
       grind)
    | exact superpose eq87 eq153
    | exact resolve eq153 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq282 : ∀ X0 X1 X2 : G, (σ (σ X0)) = (M.op (σ (σ X0)) (M.op X1 (M.op X2 (σ (σ (M.op X0 X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 (σ X0) X1 X2
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq68
    | exact resolve eq68 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq608 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq198 X1 X0
       grind)
    | exact superpose eq198 eq43
    | (have j1 := eq198 X1 X0
       grind)
    | exact resolve eq43 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq738 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq120 x X2 X0 X1
       grind)
    | exact superpose eq120 eq9
    | exact resolve eq9 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq783 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X2 X0
       have i₂ := eq738 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq738 eq9
    | exact resolve eq9 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1457 : ∀ X0 X1 X2 : G, (M.op X1 (σ (σ (M.op X0 X0)))) = (M.op (M.op X1 (σ (σ (M.op X0 X0)))) (M.op X2 (σ (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (σ (σ (M.op X0 X0)))) X2 (σ (σ X0))
       have i₂ := eq282 X0 (M.op X1 (σ (σ (M.op X0 X0)))) X1
       grind)
    | exact superpose eq282 eq9
    | exact resolve eq9 eq282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq2606 : ∀ X0 X1 X2 X3 : G, (M.op (k (σ X0) X1) (σ X2)) ≠ (M.op (k (σ X0) X1) X3) ∨ (M.op (k (σ X0) X1) (σ X2)) = (k (k (σ X0) X1) X3) ∨ (M.op (k (σ X0) X1) (σ X2)) = (M.op X3 (k (σ X0) X1)) ∨ (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (k (σ X0) X1) X1
       have i₂ := eq200 X0 X1 X2
       grind)
    | exact superpose eq200 eq13
    | (have j0 := eq13 (k (σ X0) X1) (σ X2)
       have j1 := eq200 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq200 X0 X1 X2
       grind)
    | exact resolve eq13 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2664 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (σ X2)) ≠ (M.op (σ X2) (k (σ X0) X1)) ∨ (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq200 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq3328 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X2 (σ (M.op X0 X0)))))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq608 X0 (M.op X1 (M.op X2 (σ (M.op X0 X0))))
       have i₂ := eq68 X0 X1 X2
       grind)
    | exact superpose eq68 eq608
    | exact resolve eq608 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq608
  have eq3386 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (τ (M.op X1 (M.op X2 (σ (M.op X0 X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3328 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3328
    | (have j0 := eq3328 X0 X1 X2
       grind)
    | exact resolve eq3328 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3328
  have eq5027 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq738 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) X1 X2
       have i₂ := eq783 (M.op X1 X2) X0 (M.op X1 X2)
       grind)
    | exact superpose eq783 eq738
    | exact resolve eq738 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738 eq783
  have eq5148 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 (M.op X2 X0)) X3 X0
       have i₂ := eq5027 X1 X2 X0
       grind)
    | exact superpose eq5027 eq9
    | exact resolve eq9 eq5027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5027
  have eq13668 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (k X0 (τ (M.op X1 (M.op X2 (σ (M.op X0 X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq3386 X0 X1 X2
       grind)
    | exact superpose eq3386 eq10
    | (have j1 := eq3386 X0 X1 X2
       grind)
    | exact resolve eq10 eq3386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3386
  have eq13752 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X2 (σ (M.op X0 X0)))))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13668 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13668
    | (have j0 := eq13668 X0 X1 X2
       grind)
    | exact resolve eq13668 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13668
  have eq14170 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (τ (M.op X1 (M.op X2 (σ (M.op (τ X0) (τ X0)))))))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (τ (M.op X1 (M.op X2 (σ (M.op (τ X0) (τ X0))))))
       have i₂ := eq13752 (τ X0) X1 X2
       grind)
    | exact superpose eq13752 eq17
    | (have j1 := eq13752 (τ X0) X1 X2
       grind)
    | exact resolve eq17 eq13752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13752
  have eq14246 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (M.op X1 (M.op X2 (σ (M.op (τ X0) (τ X0)))))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14170 X0 X1 X2
       have i₂ := eq11 (M.op X1 (M.op X2 (σ (M.op (τ X0) (τ X0)))))
       grind)
    | exact superpose eq11 eq14170
    | (have j0 := eq14170 X0 X1 X2
       grind)
    | exact resolve eq14170 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14170
  have eq14299 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14246 X0 X1 X2
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq14246
    | (have j0 := eq14246 X0 X1 X2
       grind)
    | exact resolve eq14246 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq14246
  have eq14347 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14299 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14299
    | (have j0 := eq14299 X0 X1 X2
       grind)
    | exact resolve eq14299 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14299
  have eq14381 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14347 X0 X1 X2
       have i₂ := eq87 X0
       grind)
    | exact superpose eq87 eq14347
    | (have j0 := eq14347 X0 X1 X2
       grind)
    | exact resolve eq14347 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14347
  have eq16107 : ∀ X0 X1 X2 X3 : G, (τ X2) = (τ (M.op X2 X2)) ∨ (k X2 (M.op X3 (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14381 X2 X3 (M.op X0 (M.op X1 X2))
       have i₂ := eq5148 X2 X0 X1 X2
       grind)
    | exact superpose eq5148 eq14381
    | (have j0 := eq14381 X2 X1 X2
       grind)
    | exact resolve eq14381 eq5148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5148 eq14381
  have eq17402 : ∀ X0 X1 X2 X3 : G, (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (k X0 (M.op X1 (M.op X2 (M.op X3 X0)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq261 X2
       have i₂ := eq16107 X0 X1 X2 X3
       grind)
    | exact superpose eq16107 eq261
    | (have j1 := eq16107 X2 X3 X0 X1
       grind)
    | exact resolve eq261 eq16107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq16107
  have eq17574 : ∀ X0 X1 X2 X3 : G, (τ (M.op (τ X0) (τ X0))) = (τ (τ X0)) ∨ (k X0 (M.op X1 (M.op X2 (M.op X3 X0)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17402 X0 X1 X2 X3
       have i₂ := eq87 (τ X0)
       grind)
    | exact superpose eq87 eq17402
    | (have j0 := eq17402 X0 X1 X2 X3
       grind)
    | exact resolve eq17402 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17402
  have eq17584 : ∀ X0 X1 X2 X3 : G, (τ (τ X0)) = (τ (τ (M.op X0 X0))) ∨ (k X0 (M.op X1 (M.op X2 (M.op X3 X0)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17574 X0 X1 X2 X3
       have i₂ := eq87 X0
       grind)
    | exact superpose eq87 eq17574
    | (have j0 := eq17574 X0 X1 X2 X3
       grind)
    | exact resolve eq17574 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq17574
  have eq39795 : ∀ X0 X1 X2 X3 : G, (τ (τ (σ X0))) = (τ (τ (σ (M.op X0 X0)))) ∨ (σ X0) = (k (σ X0) (M.op X1 (M.op X2 (M.op X3 (σ X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17584 (σ X0) X1 X2 X3
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq17584
    | (have j0 := eq17584 (σ X0) X1 X2 X3
       grind)
    | exact resolve eq17584 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17584
  have eq40050 : ∀ X0 X1 X2 X3 : G, (τ (M.op X0 X0)) = (τ (τ (σ X0))) ∨ (σ X0) = (k (σ X0) (M.op X1 (M.op X2 (M.op X3 (σ X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq39795 X0 X1 X2 X3
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq39795
    | (have j0 := eq39795 X0 X1 X2 X3
       grind)
    | exact resolve eq39795 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39795
  have eq40077 : ∀ X0 X1 X2 X3 : G, (σ X0) = (k (σ X0) (M.op X1 (M.op X2 (M.op X3 (σ X0))))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq40050 X0 X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq40050
    | (have j0 := eq40050 X0 X1 X2 X3
       grind)
    | exact resolve eq40050 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40050
  have eq57965 : ∀ X0 X1 X2 : G, (σ X1) = (k (σ X1) (M.op X2 (M.op X0 (σ (M.op X1 X1))))) ∨ (τ X1) = (τ (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40077 X1 X2 (M.op X0 (σ (M.op X1 X1))) x
       have i₂ := eq114 X1 X0 x
       grind)
    | exact superpose eq114 eq40077
    | (have j0 := eq40077 X1 X1 X2 x
       grind)
    | exact resolve eq40077 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq40077
  have eq60001 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X2 (σ (M.op X0 X0)))))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43 X0 (M.op X1 (M.op X2 (σ (M.op X0 X0))))
       have i₂ := eq57965 X2 X0 X1
       grind)
    | exact superpose eq57965 eq43
    | (have j1 := eq57965 X0 X0 X2
       grind)
    | exact resolve eq43 eq57965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57965
  have eq60054 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X2 (σ (M.op X0 X0)))))) = X0 ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60001 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq60001
    | (have j0 := eq60001 X0 X1 X2
       grind)
    | exact resolve eq60001 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60001
  have eq60242 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 (M.op X2 (σ (M.op (σ X0) (σ X0)))))))) ∨ (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43 X0 (τ (M.op X1 (M.op X2 (σ (M.op (σ X0) (σ X0))))))
       have i₂ := eq60054 (σ X0) X1 X2
       grind)
    | exact superpose eq60054 eq43
    | (have j1 := eq60054 (σ X0) X1 X2
       grind)
    | exact resolve eq43 eq60054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq60054
  have eq60388 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 (M.op X2 (σ (σ (M.op X0 X0)))))))) ∨ (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60242 X0 X1 X2
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq60242
    | (have j0 := eq60242 X0 X1 X2
       grind)
    | exact resolve eq60242 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60242
  have eq60471 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (M.op X1 (M.op X2 (σ (σ (M.op X0 X0)))))))) = X0 ∨ (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60388 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq60388
    | (have j0 := eq60388 X0 X1 X2
       grind)
    | exact resolve eq60388 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60388
  have eq60542 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (k X0 (τ (τ (M.op X1 (M.op X2 (σ (σ (M.op X0 X0)))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60471 X0 X1 X2
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq60471
    | (have j0 := eq60471 X0 X1 X2
       grind)
    | exact resolve eq60471 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60471
  have eq60591 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (k X0 (τ (τ (M.op X1 (M.op X2 (σ (σ (M.op X0 X0)))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60542 X0 X1 X2
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq60542
    | (have j0 := eq60542 X0 X1 X2
       grind)
    | exact resolve eq60542 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60542
  have eq60627 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (M.op X1 (M.op X2 (σ (σ (M.op X0 X0)))))))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60591 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq60591
    | (have j0 := eq60591 X0 X1 X2
       grind)
    | exact resolve eq60591 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60591
  have eq61625 : ∀ X0 X1 : G, (k X1 (τ (τ (M.op X0 (σ (σ (M.op (M.op X1 X1) (M.op X1 X1)))))))) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60627 X1 (M.op X0 (σ (σ (M.op (M.op X1 X1) (M.op X1 X1))))) x
       have i₂ := eq1457 (M.op X1 X1) X0 x
       grind)
    | exact superpose eq1457 eq60627
    | (have j0 := eq60627 X1 X1 x
       grind)
    | exact resolve eq60627 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1457 eq60627
  have eq79234 : ∀ X0 X1 X2 : G, (M.op (σ X2) (k X0 X1)) ≠ (M.op (k X0 X1) (σ X2)) ∨ (M.op (k X0 X1) (k X0 X1)) = (M.op (σ X2) (k X0 X1)) ∨ (σ (k (k (τ X0) (τ X1)) X2)) = (M.op (k X0 X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2664 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2664
    | exact resolve eq2664 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2664
  have eq79412 : ∀ X0 X1 X2 : G, (σ (k (τ (k X0 X1)) X2)) = (M.op (k X0 X1) (σ X2)) ∨ (M.op (σ X2) (k X0 X1)) ≠ (M.op (k X0 X1) (σ X2)) ∨ (M.op (k X0 X1) (k X0 X1)) = (M.op (σ X2) (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79234 X0 X1 X2
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq79234
    | (have j0 := eq79234 X0 X1 X2
       grind)
    | exact resolve eq79234 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq79234
  have eq79483 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (M.op (k X0 X1) (σ X2)) ∨ (M.op (σ X2) (k X0 X1)) ≠ (M.op (k X0 X1) (σ X2)) ∨ (M.op (k X0 X1) (k X0 X1)) = (M.op (σ X2) (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79412 X0 X1 X2
       have i₂ := eq17 (k X0 X1) X2
       grind)
    | exact superpose eq17 eq79412
    | (have j0 := eq79412 X0 X1 X2
       grind)
    | exact resolve eq79412 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq79412
  have eq79531 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (M.op (k X0 X1) (σ X2)) ∨ (M.op (σ X2) (k X0 X1)) ≠ (M.op (k X0 X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq79483 X0 X1 X2
       have j1 := eq12 (k X0 X1) (σ X2)
       grind)
    | (have r₁ := eq79483 X0 X1 X2
       have r₂ := eq12 (k X0 X1) (σ X2)
       grind)
    | exact resolve eq79483 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79483
  have eq260343 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (M.op (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2606 X0 X1 X2 (σ X2)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2606
  have eq260345 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (M.op (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq260343 X0 X1 X2
       have j1 := eq12 (k (σ X0) X1) (σ X2)
       grind)
    | (have r₁ := eq260343 X0 X1 X2
       have r₂ := eq12 (k (σ X0) X1) (σ X2)
       grind)
    | exact resolve eq260343 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260343
  have eq260480 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq260345 X0 X1 X2
       have j1 := eq79531 (σ X0) X1 X2
       grind)
    | (have r₁ := eq260345 X0 X1 X2
       have r₂ := eq79531 (σ X0) X1 X2
       grind)
    | exact resolve eq260345 eq79531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79531 eq260345
  have eq260580 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq260480 X0 X1 X2
       have i₂ := eq42 X0 X1 X2
       grind)
    | exact superpose eq42 eq260480
    | (have j0 := eq260480 X0 X1 X2
       grind)
    | exact resolve eq260480 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq260480
  have eq260581 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq260580 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260580
  have eq260804 : ∀ X0 X1 X2 : G, (σ (k (k X1 X0) X2)) = (M.op (k (σ X1) (σ X0)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq260581 X1 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq260581
    | exact resolve eq260581 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261117 : ∀ X0 X1 X2 : G, (k (σ (k X0 (τ X1))) X2) = (M.op (k (σ X0) X1) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X2 (k X0 (τ X1))
       have i₂ := eq260581 X0 X1 (τ X2)
       grind)
    | exact superpose eq260581 eq18
    | exact resolve eq18 eq260581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260581
  have eq261514 : ∀ X0 X1 X2 : G, (k (σ (k X0 (τ X1))) X2) = (M.op (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq261117 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq261117
    | exact resolve eq261117 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261117
  have eq261739 : ∀ X0 X1 X2 : G, (σ (k (k X1 X0) X2)) = (M.op (σ (k X1 X0)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq260804 X0 X1 X2
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq260804
    | exact resolve eq260804 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260804
  have eq261792 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) X2) = (M.op (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq261514 X0 X1 X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq261514
    | exact resolve eq261514 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq261514
  have eq262064 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (M.op (k X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq261792 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq261792
    | exact resolve eq261792 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262183 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X0)) X1) = (M.op (M.op (σ X0) (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq261792 X0 (σ X0) x
       have i₂ := eq28 (σ X0)
       grind)
    | exact superpose eq28 eq261792
    | exact resolve eq261792 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261792
  have eq262932 : ∀ X0 X1 : G, (k (σ (M.op X0 X0)) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq262183 X0 X1
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq262183
    | exact resolve eq262183 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq262183
  have eq265934 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq262064 X0 X0 x
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq262064
    | exact resolve eq262064 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq265987 : ∀ X0 X2 : G, (k X0 X2) = (M.op X0 X2) ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq262064 x (τ (τ (M.op X0 (σ (σ (M.op (M.op x x) (M.op x x))))))) X2
       have i₂ := eq61625 X0 x
       grind)
    | exact superpose eq61625 eq262064
    | (have j1 := eq61625 X0 X0
       grind)
    | exact resolve eq262064 eq61625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262064
  have eq276010 : ∀ X0 X1 : G, (σ (k (M.op X0 X0) X1)) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op X0 X0) X1
       have i₂ := eq262932 X0 (σ X1)
       grind)
    | exact superpose eq262932 eq15
    | exact resolve eq15 eq262932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262932
  have eq276471 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X1)) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq276010 X0 X1
       have i₂ := eq265934 X0 X1
       grind)
    | exact superpose eq265934 eq276010
    | exact resolve eq276010 eq265934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265934 eq276010
  have eq281210 : ∀ X0 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq261739 (τ (τ (M.op X0 (σ (σ (M.op (M.op x x) (M.op x x))))))) x X2
       have i₂ := eq61625 X0 x
       grind)
    | exact superpose eq61625 eq261739
    | (have j1 := eq61625 X0 X0
       grind)
    | exact resolve eq261739 eq61625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61625 eq261739
  have eq366095 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq281210 x y
       grind)
    | exact superpose eq281210 eq16
    | (have j1 := eq281210 x x
       grind)
    | exact resolve eq16 eq281210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281210
  have eq368197 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq366095
       have i₂ := eq265987 x y
       grind)
    | exact superpose eq265987 eq366095
    | (have j1 := eq265987 x x
       grind)
    | exact resolve eq366095 eq265987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265987 eq366095
  have eq368206 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq368197
  have eq368207 : x = (M.op x x) := by grind
  clear eq368206
  have eq368371 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq276471 x x
       have i₂ := eq368207
       grind)
    | exact superpose eq368207 eq276471
    | exact resolve eq276471 eq368207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276471 eq368207
  have eq417406 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq368371 y
       grind)
    | exact superpose eq368371 eq16
    | (have r₁ := eq16
       have r₂ := eq368371 y
       grind)
    | exact resolve eq16 eq368371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368371
  have eq417934 : False := by grind
  exact eq417934

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_y_pxy_y_pyx_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq48 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k (M.op X1 (M.op X2 (M.op X0 X0))) X0) = X0 ∨ (M.op (M.op X1 (M.op X2 (M.op X0 X0))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 (M.op X2 (M.op X0 X0))) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op X1 (M.op X2 (M.op X0 X0))) X0
       grind)
    | (have r₁ := eq13 (M.op X1 (M.op X2 (M.op X0 X0))) X0
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X2 (M.op X0 X0))) X0) = X0 ∨ (M.op (M.op X1 (M.op X2 (M.op X0 X0))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq48 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq76 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq117 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
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
  have eq232 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq76 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq12
    | (have j1 := eq76 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq76 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq12 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq241 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq232 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq247 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq241 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq241
    | (have j0 := eq241 X0 X1
       grind)
    | exact resolve eq241 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq248 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq247 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq756 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq248 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq248
    | exact resolve eq248 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq248 x y
       grind)
    | exact superpose eq248 eq16
    | (have j1 := eq248 x y
       grind)
    | exact resolve eq16 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq789 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq248 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq810 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq756 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq756
    | (have j0 := eq756 X0 X1
       grind)
    | exact resolve eq756 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq756
  have eq933 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq810 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq810
    | exact resolve eq810 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq1005 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq933 (τ X1) X0
       grind)
    | exact superpose eq933 eq17
    | (have j1 := eq933 (τ X1) X0
       grind)
    | exact resolve eq17 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq933
  have eq1049 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq117 x X2 X0 X1
       grind)
    | exact superpose eq117 eq9
    | exact resolve eq9 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq1092 : ∀ X0 X2 : G, (M.op X2 X0) = (k X0 (M.op X2 X0)) ∨ (M.op X2 X0) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq51 (M.op x X2) X2 X0
       have i₂ := eq1049 X0 x X2
       grind)
    | exact superpose eq1049 eq51
    | exact resolve eq51 eq1049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1049
  have eq1565 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1005 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1005
    | exact resolve eq1005 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq1629 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1565 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1565
    | (have j0 := eq1565 X0 X1
       grind)
    | exact resolve eq1565 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565
  have eq1805 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq771
       have i₂ := eq1629 y x
       grind)
    | exact superpose eq1629 eq771
    | (have j1 := eq1629 (σ y) (σ x)
       grind)
    | (have r₁ := eq771
       have r₂ := eq1629 y x
       grind)
    | exact resolve eq771 eq1629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq1806 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1805
  have eq1809 : x ≠ x ∨ x = (k y x) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1806
       grind)
    | exact superpose eq1806 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1806
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1806
       grind)
    | exact resolve eq13 eq1806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1814 : x = (M.op y x) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1809
  have eq5735 : x ≠ (M.op x y) ∨ x = (k y x) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1814
       grind)
    | exact superpose eq1814 eq12
    | exact resolve eq12 eq1814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814
  have eq5748 : x ≠ (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5735
  have eq5753 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq5748
       have r₂ := eq1806
       grind)
    | exact resolve eq5748 eq1806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1806 eq5748
  have eq5758 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq789 x y
       have i₂ := eq5753
       grind)
    | exact superpose eq5753 eq789
    | (have j0 := eq789 x y
       grind)
    | exact resolve eq789 eq5753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789 eq5753
  have eq5779 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5758
  have eq5780 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5779
  have eq5981 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5780
       grind)
    | exact superpose eq5780 eq16
    | exact resolve eq16 eq5780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5994 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1092 (σ y) (σ x)
       have i₂ := eq5780
       grind)
    | exact superpose eq5780 eq1092
    | exact resolve eq1092 eq5780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092
  have eq5999 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq5994
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq5994
    | exact resolve eq5994 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5994
  have eq6759 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq5999
       grind)
    | exact superpose eq5999 eq12
    | exact resolve eq12 eq5999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5999
  have eq6788 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq6759
       have r₂ := eq5780
       grind)
    | exact resolve eq6759 eq5780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5780 eq6759
  have eq6799 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq6788
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq6788
    | exact resolve eq6788 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6788
  have eq6800 : (σ x) = (σ (k y x)) := by grind
  clear eq6799
  have eq7011 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1629 y x
       have i₂ := eq6800
       grind)
    | exact superpose eq6800 eq1629
    | (have j0 := eq1629 y x
       grind)
    | exact resolve eq1629 eq6800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1629 eq6800
  have eq7087 : x = (M.op x y) := by
    first
    | (have r₁ := eq7011
       have r₂ := eq5981
       grind)
    | exact resolve eq7011 eq5981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7011
  have eq7331 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq5981
       have i₂ := eq7087
       grind)
    | exact superpose eq7087 eq5981
    | exact resolve eq5981 eq7087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5981 eq7087
  have eq7346 : False := by grind
  exact eq7346

/-- `Equation4574`: `x ◇ (y ◇ z) = (w ◇ w) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pyx_pxx_pxy_Equation4574 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4574 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4574.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X3 X3) X2) := by
    intro X0 X1 X2 X3
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
  have eq51 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X5 X5) X2) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X3 (M.op x x) X2 X5
       have i₂ := eq14 X0 X1 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X1 X1) y) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (M.op (M.op (M.op X0 X0) X1) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X2 X3 X4 (M.op x X1)
       have i₂ := eq14 (M.op x X1) x X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) ≠ (M.op X3 X1) ∨ (k X2 (M.op X3 X1)) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X2 (M.op X3 X1)
       have i₂ := eq14 X2 X3 X1 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op X3 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X3 X3) X2)
       have r₂ := eq14 X0 (M.op X3 X3) X2 X3
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ (k y (k x x))) = (k (σ y) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq36 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq36
    | exact resolve eq36 eq43
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
  have eq80 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq81 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq83 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq84 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq88 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq95 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq88
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq97
    | exact resolve eq97 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
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
  have eq113 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq80
       grind)
    | exact superpose eq80 eq16
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq81 eq16
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq163 : ∀ X0 : G, (σ (k X0 (k (M.op x y) (M.op x y)))) = (k (σ X0) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq142 eq10
    | exact resolve eq10 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq142 eq16
    | exact resolve eq16 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 X1 X3 : G, (M.op X3 (M.op x y)) = (M.op (M.op (M.op X0 X0) X1) y) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq52 X3 (M.op x X1)
       have i₂ := eq14 (M.op x X1) x X1 X0
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op X2 (M.op x y)) := by
    intro X0 X2
    first
    | (have i₁ := eq52 X2 x
       have i₂ := eq52 X0 x
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X1 X3 : G, (M.op X3 (M.op x y)) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq52 X3 x
       have i₂ := eq14 X0 X1 y x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 : G, (M.op x y) ≠ (M.op (M.op X0 X0) y) ∨ (M.op (M.op x y) X1) = (k X1 (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq13
    | (have j0 := eq13 X1 (M.op x y)
       grind)
    | exact resolve eq13 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X2 (M.op (σ x) (σ y))) := by
    intro X0 X2
    first
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : ∀ X0 X1 X3 : G, (M.op X3 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq53 X0 X3
       have i₂ := eq14 X0 X1 sF3 X3
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) y) := by
    intro X0 X1
    first
    | exact superpose eq259 eq52
    | exact resolve eq52 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1186 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op (M.op X0 (M.op (σ x) (σ y))) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1921 : ∀ X0 X1 X3 : G, (M.op (M.op X1 X1) y) ≠ (M.op X0 (M.op x y)) ∨ (M.op (M.op X0 (M.op x y)) X3) = (k X3 (M.op X0 (M.op x y))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq69 X0 y x (M.op X1 X1)
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq69
    | (have j0 := eq69 X0 (M.op x y) X3 X0
       grind)
    | exact resolve eq69 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1929 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X1) X2)) = (M.op (M.op (M.op X1 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq69 X0 X2 X0 (M.op X1 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq1937 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op x y)) X3) = (k X3 (M.op X0 (M.op x y))) := by
    intro X0 X3
    first
    | (have j0 := eq1921 X0 x X3
       grind)
    | (have r₁ := eq1921 X0 x X3
       have r₂ := eq52 X0 x
       grind)
    | exact resolve eq1921 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921
  have eq1992 : ∀ X0 X1 X2 X4 X5 : G, (M.op X0 (M.op X1 (M.op X2 (M.op x y)))) = (M.op (M.op (M.op X4 X4) X5) y) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq219 X0 X1 (M.op X5 X5)
       have i₂ := eq51 X0 X1 sF0 x X5
       grind)
    | exact superpose eq51 eq219
    | exact resolve eq219 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq219
  have eq2502 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq82 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq82 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq2528 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2502 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq2502 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq2502 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq2502 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2502
  have eq2538 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2528 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq2528
    | (have j0 := eq2528 X0 X1
       grind)
    | exact resolve eq2528 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2528
  have eq4245 : ∀ X0 X1 X4 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X1) = (M.op (M.op X4 (M.op (σ x) (σ y))) X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq1186 X4 x x X1
       have i₂ := eq1186 X0 x x X1
       grind)
    | exact superpose eq1186 eq1186
    | exact resolve eq1186 eq1186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq46477 : (τ (k (σ x) (σ x))) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq95
       grind)
    | exact superpose eq95 eq16
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq46502 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq49 eq46477
    | exact resolve eq46477 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq46477
  have eq46505 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq46502
       have r₂ := eq13 x x
       grind)
    | exact resolve eq46502 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46502
  have eq46506 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq46505
       grind)
    | exact superpose eq46505 eq43
    | exact resolve eq43 eq46505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46508 : (k (σ y) (k (σ x) (σ x))) = (σ (k y (M.op x x))) := by
    first
    | (have i₁ := eq76
       have i₂ := eq46505
       grind)
    | exact superpose eq46505 eq76
    | exact resolve eq76 eq46505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq47611 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47612 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq47611
    | exact resolve eq47611 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47611
  have eq47623 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq47612
       have r₂ := eq27
       grind)
    | exact resolve eq47612 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47612
  have eq47625 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq47623
    | exact resolve eq47623 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47623
  have eq47627 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq47625 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq47625
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq47625
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq47625
       grind)
    | exact resolve eq12 eq47625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47629 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ x)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq47625 eq14
    | exact resolve eq14 eq47625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47667 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq47627
  have eq47669 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq47667
    | exact resolve eq47667 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47667
  have eq47670 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq47669
  have eq48317 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq47670 eq100
    | exact resolve eq100 eq47670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq47670
  have eq48325 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq48317
  have eq49404 : ∀ X0 X2 : G, (M.op X0 (σ x)) = (M.op X2 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0 X2
    first
    | exact superpose eq47629 eq47629
    | exact resolve eq47629 eq47629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47629
  have eq49759 : ∀ X0 X2 : G, (M.op X0 (σ x)) = (M.op X2 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0 X2
    first
    | (have j0 := eq49404 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49404
  have eq50237 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq49759 eq48325
    | exact resolve eq48325 eq49759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50238 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq49759 eq47625
    | exact resolve eq47625 eq49759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47625 eq49759
  have eq50239 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq50238 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50238
  have eq50240 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq50237 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50237
  have eq50505 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq50239 eq48325
    | exact resolve eq48325 eq50239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50239
  have eq50506 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq50505
  have eq50542 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq50506
       grind)
    | exact superpose eq50506 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq50506
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq50506
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq50506
       grind)
    | exact resolve eq13 eq50506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50543 : ∀ X0 X1 : G, (M.op (M.op X1 X1) x) = (M.op X0 x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 y x X1
       have i₂ := eq50506
       grind)
    | exact superpose eq50506 eq14
    | exact resolve eq14 eq50506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50581 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq50542
  have eq50584 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50581
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50581
    | exact resolve eq50581 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50581
  have eq51031 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq79
       have i₂ := eq50584
       grind)
    | exact superpose eq50584 eq79
    | exact resolve eq79 eq50584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq50584
  have eq51048 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq51031
    | exact resolve eq51031 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51031
  have eq51078 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op X0 (M.op X1 (σ x))) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq50240 (M.op x x)
       have i₂ := eq14 X0 X1 sF2 x
       grind)
    | exact superpose eq14 eq50240
    | exact resolve eq50240 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50240
  have eq56176 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq83 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq83
    | (have j0 := eq83 x
       grind)
    | exact resolve eq83 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq56222 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq56176
  have eq56227 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq56222
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq56222
    | exact resolve eq56222 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq56222
  have eq56253 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq56227
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq56227 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56227
  have eq56757 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq84 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq84
    | (have j0 := eq84 y
       grind)
    | exact resolve eq84 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq56802 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq56757
  have eq56806 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq56802
       have i₂ := eq80
       grind)
    | exact superpose eq80 eq56802
    | exact resolve eq56802 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56802
  have eq56833 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq56806
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq56806 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56806
  have eq56909 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq48325 eq51078
    | exact resolve eq51078 eq48325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48325 eq51078
  have eq57227 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq56909 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56909
  have eq57588 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq143
    | (have j0 := eq143 (M.op x y)
       grind)
    | exact resolve eq143 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq57632 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq57588
  have eq57635 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq142 eq57632
    | exact resolve eq57632 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57632
  have eq57663 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq57635
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq57635 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57635
  have eq58398 : ∀ X0 X2 : G, (M.op X2 x) = (M.op X0 x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X2
    first
    | (have i₁ := eq50543 X0 x
       have i₂ := eq50543 X2 x
       grind)
    | (have i₁ := eq50543 X0 x
       have i₂ := eq50543 (M.op x x) x
       grind)
    | exact superpose eq50543 eq50543
    | exact resolve eq50543 eq50543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50543
  have eq58767 : ∀ X0 X2 : G, (M.op X2 x) = (M.op X0 x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X2
    first
    | (have j0 := eq58398 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58398
  have eq59300 : ∀ X0 : G, x = (M.op X0 x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq50506
       have i₂ := eq58767 X0 y
       grind)
    | (have i₁ := eq50506
       have i₂ := eq58767 y X0
       grind)
    | exact superpose eq58767 eq50506
    | exact resolve eq50506 eq58767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50506 eq58767
  have eq59303 : ∀ X0 : G, x = (M.op X0 x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq59300 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59300
  have eq59399 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op x X2) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 X2 x
       have i₂ := eq59303 x
       grind)
    | exact superpose eq59303 eq14
    | exact resolve eq14 eq59303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59587 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46506
       have i₂ := eq59303 x
       grind)
    | exact superpose eq59303 eq46506
    | exact resolve eq46506 eq59303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59303
  have eq59618 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq59587
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq59587
    | exact resolve eq59587 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59587
  have eq60381 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq59618 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq59618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59618
  have eq60382 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq60381
  have eq108738 : ∀ X0 : G, (σ (k X0 (k (M.op x y) (M.op x y)))) = (k (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq57663 eq163
    | exact resolve eq163 eq57663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq219203 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op x (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq60382 eq59399
    | exact resolve eq59399 eq60382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220038 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op x (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq219203 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219203
  have eq220993 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X1 (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq220038 eq220038
    | exact resolve eq220038 eq220038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221325 : (σ x) = (M.op x (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq220038 eq60382
    | exact resolve eq60382 eq220038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60382 eq220038
  have eq221436 : (σ x) = (M.op x (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq221325
  have eq221460 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X1 (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq220993 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220993
  have eq221585 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq221436 eq59399
    | exact resolve eq59399 eq221436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59399 eq221436
  have eq221586 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq221585 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221585
  have eq225145 : ∀ X0 X1 : G, (σ x) ≠ (M.op X0 (σ x)) ∨ (k X1 (σ x)) = (M.op (σ x) X1) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq221460 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq221460 X0 X1
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq221460 X0 X1
       grind)
    | exact resolve eq13 eq221460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221460
  have eq225567 : ∀ X1 : G, (k X1 (σ x)) = (M.op (σ x) X1) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have j0 := eq225145 x X1
       grind)
    | (have r₁ := eq225145 x X1
       have r₂ := eq221586 x
       grind)
    | exact resolve eq225145 eq221586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221586 eq225145
  have eq234349 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq225567 eq51048
    | exact resolve eq51048 eq225567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51048 eq225567
  have eq234402 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq234349
  have eq234441 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq234402
    | exact resolve eq234402 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234402
  have eq234478 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq234441
       have r₂ := eq27
       grind)
    | exact resolve eq234441 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234441
  have eq234490 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq234478 eq259
    | exact resolve eq259 eq234478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234786 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq234490
    | (have j0 := eq234490 X0 (σ x)
       grind)
    | exact resolve eq234490 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234490
  have eq236464 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq53 eq234786
    | exact resolve eq234786 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236681 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq234786 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq234786 X0
       grind)
    | exact resolve eq13 eq234786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234786
  have eq237147 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq236681 X0
       grind)
    | (have r₁ := eq236681 X0
       have r₂ := eq234478
       grind)
    | exact resolve eq236681 eq234478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236681
  have eq237152 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq234478 eq236464
    | exact resolve eq236464 eq234478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234478 eq236464
  have eq237718 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq237152 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237152
  have eq249780 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq237147 eq113
    | exact resolve eq113 eq237147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq237147
  have eq257392 : (τ (σ y)) = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq237718 eq249780
    | exact resolve eq249780 eq237718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237718 eq249780
  have eq257439 : (τ (σ y)) = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq257392
  have eq257451 : y = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq257439
    | exact resolve eq257439 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257439
  have eq257469 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq257451
       grind)
    | exact superpose eq257451 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq257451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257451
  have eq257493 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq257469
  have eq257541 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq222 X1 y X0
       have i₂ := eq257493
       grind)
    | exact superpose eq257493 eq222
    | exact resolve eq222 eq257493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq258136 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq257541 X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq257541
    | (have j0 := eq257541 X0 x
       grind)
    | exact resolve eq257541 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259034 : ∀ X0 : G, y = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq257493
       have i₂ := eq257541 X0 y
       grind)
    | exact superpose eq257541 eq257493
    | exact resolve eq257493 eq257541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257493 eq257541
  have eq259201 : ∀ X0 : G, y = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq259034 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259034
  have eq260394 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq259201 eq258136
    | exact resolve eq258136 eq259201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258136 eq259201
  have eq260735 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq260394
  have eq260839 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq260735 eq28
    | exact resolve eq28 eq260735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq260735
  have eq261088 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq260839
    | exact resolve eq260839 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq260839
  have eq261098 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq261088 eq20
    | exact resolve eq20 eq261088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261104 : (σ (k y y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq261088 eq81
    | exact resolve eq81 eq261088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261117 : (σ (k y y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq261088 eq142
    | exact resolve eq142 eq261088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261147 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq261088 eq221
    | exact resolve eq221 eq261088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261219 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq261262 : (σ (k y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57663 eq261117
    | exact resolve eq261117 eq57663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261117
  have eq261274 : (k (σ y) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq261104
       have i₂ := eq80
       grind)
    | exact superpose eq80 eq261104
    | exact resolve eq261104 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261104
  have eq261278 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq261098
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq261098
    | exact resolve eq261098 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261098
  have eq261298 : (k (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq261262
       have i₂ := eq80
       grind)
    | exact superpose eq80 eq261262
    | exact resolve eq261262 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq261262
  have eq261305 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56833 eq261274
    | exact resolve eq261274 eq56833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261274
  have eq261314 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56833 eq261298
    | exact resolve eq261298 eq56833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56833 eq261298
  have eq261317 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq261278 eq26
    | exact resolve eq26 eq261278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261333 : (k y (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq261278 eq120
    | exact resolve eq120 eq261278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261682 : (k y (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq165 eq261333
    | exact resolve eq261333 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq261333
  have eq262713 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq261147 X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq261147
    | (have j0 := eq261147 X0 x
       grind)
    | exact resolve eq261147 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261147
  have eq264237 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq262713 (M.op x x)
       have i₂ := eq52 X0 x
       grind)
    | exact superpose eq52 eq262713
    | exact resolve eq262713 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264386 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq53 X0 y
       have i₂ := eq262713 y
       grind)
    | exact superpose eq262713 eq53
    | exact resolve eq53 eq262713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264931 : ∀ X0 : G, y = (M.op X0 y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq261088 eq264237
    | exact resolve eq264237 eq261088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264237
  have eq265552 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq264931 X0
       grind)
    | (have r₁ := eq264931 X0
       have r₂ := eq261219
       grind)
    | exact resolve eq264931 eq261219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264931
  have eq267688 : ∀ X0 : G, (M.op x y) ≠ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq261314 eq230
    | (have j0 := eq230 (σ (M.op x y)) X0
       grind)
    | exact resolve eq230 eq261314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq261314
  have eq267837 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq267688 X0
       grind)
    | (have r₁ := eq267688 X0
       have r₂ := eq262713 (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq267688 eq262713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267688
  have eq268920 : (σ (k y (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq261682 eq142
    | exact resolve eq142 eq261682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261682
  have eq268991 : (σ (k y (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57663 eq268920
    | exact resolve eq268920 eq57663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268920
  have eq269016 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq81 eq268991
    | exact resolve eq268991 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268991
  have eq271422 : (k (σ y) (σ (M.op x y))) = (σ (M.op (M.op x y) y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq267837 eq81
    | exact resolve eq81 eq267837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq267837
  have eq273385 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op y (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq261088 eq264386
    | exact resolve eq264386 eq261088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273386 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op x y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq261278 eq264386
    | exact resolve eq264386 eq261278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264386
  have eq273965 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op x y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq273386 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273386
  have eq274001 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op y (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq273385 X0
       grind)
    | (have r₁ := eq273385 X0
       have r₂ := eq261219
       grind)
    | exact resolve eq273385 eq261219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273385
  have eq275938 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op y (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq261088 eq273965
    | exact resolve eq273965 eq261088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261088 eq273965
  have eq276501 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op y (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq275938 X0
       grind)
    | (have r₁ := eq275938 X0
       have r₂ := eq261219
       grind)
    | exact resolve eq275938 eq261219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261219 eq275938
  have eq280546 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq271422
       have i₂ := eq265552 sF0
       grind)
    | exact superpose eq265552 eq271422
    | exact resolve eq271422 eq265552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265552
  have eq280547 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq271422
       have i₂ := eq262713 sF0
       grind)
    | exact superpose eq262713 eq271422
    | exact resolve eq271422 eq262713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262713 eq271422
  have eq280621 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq280547
  have eq280622 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq280546
  have eq280631 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq280621
    | exact resolve eq280621 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280621
  have eq280632 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq280622
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq280622
    | exact resolve eq280622 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280622
  have eq280660 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq280631 eq261305
    | exact resolve eq261305 eq280631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261305
  have eq280661 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq280631 eq269016
    | exact resolve eq269016 eq280631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269016 eq280631
  have eq280682 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq280661
  have eq280683 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq280660
  have eq280722 : (τ (σ y)) = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq280632 eq120
    | exact resolve eq120 eq280632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq280632
  have eq280777 : y = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq280722
    | exact resolve eq280722 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280722
  have eq280870 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq280682 eq53
    | exact resolve eq53 eq280682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280682
  have eq281046 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X1 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq280683 eq260
    | exact resolve eq260 eq280683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq280683
  have eq281929 : (σ y) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq280777 eq2538
    | (have j0 := eq2538 y (M.op x y)
       grind)
    | exact resolve eq2538 eq280777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280777
  have eq281931 : (σ y) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq281929
  have eq281962 : (σ y) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq281931
    | exact resolve eq281931 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281931
  have eq281982 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq281962
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq281962
    | exact resolve eq281962 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281962
  have eq281994 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq281982
       have r₂ := eq261278
       grind)
    | exact resolve eq281982 eq261278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281982
  have eq282004 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq281994
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq281994
    | exact resolve eq281994 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281994
  have eq282014 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq282004
    | exact resolve eq282004 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282004
  have eq283316 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq280870 eq282014
    | exact resolve eq282014 eq280870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280870 eq282014
  have eq283415 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq283316 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283316
  have eq283711 : (σ y) = (M.op y (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq283415 eq274001
    | exact resolve eq274001 eq283415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274001 eq283415
  have eq284041 : (σ y) = (M.op y (σ y)) ∨ x = (M.op x y) := by grind
  clear eq283711
  have eq284189 : (σ (M.op x y)) = (M.op y (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq261278 eq284041
    | exact resolve eq284041 eq261278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261278 eq284041
  have eq284307 : (σ (M.op x y)) = (M.op y (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq284189
  have eq284572 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq284307 eq276501
    | exact resolve eq276501 eq284307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276501 eq284307
  have eq284648 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq284572 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284572
  have eq286842 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq281046 eq261317
    | exact resolve eq261317 eq281046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261317 eq281046
  have eq286846 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq286842 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286842
  have eq287209 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f287209_13 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
      intro X0
      grind
    have f287209_14 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
      intro X0
      grind
    have f287209_22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
    have f287209_24 : x ≠ (M.op x y) := by grind
    have f287209_25 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
      intro X0
      first
      | (have j0 := f287209_14 X0
         grind)
      | (have r₁ := f287209_14 X0
         have r₂ := f287209_24
         grind)
      | exact resolve f287209_14 f287209_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f287209_26 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (σ x) (σ y))) := by
      intro X0
      first
      | (have j0 := f287209_13 X0
         grind)
      | (have r₁ := f287209_13 X0
         have r₂ := f287209_24
         grind)
      | exact resolve f287209_13 f287209_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f287209_138 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
      first
      | (have i₁ := f287209_26 x
         have i₂ := f287209_25 x
         grind)
      | exact superpose f287209_25 f287209_26
      | exact resolve f287209_26 f287209_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f287209_157 : False := by
      first
      | (have r₁ := f287209_138
         have r₂ := f287209_22
         grind)
      | exact resolve f287209_138 f287209_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f287209_157
  clear eq284648 eq286846
  have eq287542 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq287209
  have eq287609 : x = (M.op x y) := by
    first
    | (have r₁ := eq287542
       have r₂ := eq27
       grind)
    | exact resolve eq287542 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287542
  have eq287614 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq287609 eq20
    | exact resolve eq20 eq287609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287616 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = (M.op X1 x) := by
    intro X0 X1
    first
    | exact superpose eq287609 eq52
    | exact resolve eq52 eq287609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq287663 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X0 x) := by
    intro X0 X1
    first
    | exact superpose eq287609 eq221
    | exact resolve eq221 eq287609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq287672 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) y) = (M.op X0 x) := by
    intro X0 X1
    first
    | exact superpose eq287609 eq281
    | exact resolve eq281 eq287609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq287705 : ∀ X0 X1 : G, (M.op (M.op X0 x) X1) = (k X1 (M.op X0 x)) := by
    intro X0 X1
    first
    | exact superpose eq287609 eq1937
    | exact resolve eq1937 eq287609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1937
  have eq287888 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq287614
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq287614
    | exact resolve eq287614 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287614
  have eq287939 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq287888 eq26
    | exact resolve eq26 eq287888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289184 : ∀ X0 : G, (k (σ x) (σ x)) = (σ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq46506
       have i₂ := eq287663 X0 x
       grind)
    | (have i₁ := eq46506
       have i₂ := eq287663 x X0
       grind)
    | exact superpose eq287663 eq46506
    | exact resolve eq46506 eq287663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46506
  have eq289212 : ∀ X0 : G, (M.op (σ x) (σ x)) = (σ (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq56253 eq289184
    | exact resolve eq289184 eq56253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289184
  have eq289315 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq287888 eq289212
    | exact resolve eq289212 eq287888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289212
  have eq289366 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq289315 (M.op x x)
       have i₂ := eq14 X0 X1 x x
       grind)
    | exact superpose eq14 eq289315
    | exact resolve eq289315 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289463 : ∀ X0 : G, (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op X0 x)
       have i₂ := eq289315 X0
       grind)
    | exact superpose eq289315 eq16
    | exact resolve eq16 eq289315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289621 : ∀ X0 X1 : G, (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op X0 (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq289463 (M.op x x)
       have i₂ := eq14 X0 X1 x x
       grind)
    | exact superpose eq14 eq289463
    | exact resolve eq289463 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290952 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op X0 X0) y)) := by
    intro X0
    first
    | (have i₁ := eq289315 x
       have i₂ := eq287616 X0 x
       grind)
    | exact superpose eq287616 eq289315
    | exact resolve eq289315 eq287616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287616 eq289315
  have eq295641 : ∀ X0 : G, (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op X0 (M.op (σ x) (σ y))) y) := by
    intro X0
    first
    | (have i₁ := eq287672 x X0
       have i₂ := eq289463 x
       grind)
    | exact superpose eq289463 eq287672
    | exact resolve eq287672 eq289463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287672 eq289463
  have eq316220 : (k (σ y) (k (σ x) (σ x))) = (σ (M.op (M.op x x) y)) := by
    first
    | (have i₁ := eq46508
       have i₂ := eq287705 x y
       grind)
    | exact superpose eq287705 eq46508
    | exact resolve eq46508 eq287705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46508
  have eq316294 : (k (σ y) (k (σ x) (σ x))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq316220
       have i₂ := eq290952 x
       grind)
    | exact superpose eq290952 eq316220
    | exact resolve eq316220 eq290952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316220
  have eq316318 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ y) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq56253 eq316294
    | exact resolve eq316294 eq56253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56253 eq316294
  have eq316335 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq287888 eq316318
    | exact resolve eq316318 eq287888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316318
  have eq330584 : ∀ X0 : G, (σ (k X0 (k x x))) = (k (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq287609 eq108738
    | exact resolve eq108738 eq287609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108738
  have eq330585 : ∀ X0 : G, (σ (k X0 (M.op x x))) = (k (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq330584 X0
       have i₂ := eq46505
       grind)
    | exact superpose eq46505 eq330584
    | exact resolve eq330584 eq46505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330584
  have eq330586 : ∀ X0 : G, (σ (M.op (M.op x x) X0)) = (k (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq330585 X0
       have i₂ := eq287705 x X0
       grind)
    | exact superpose eq287705 eq330585
    | exact resolve eq330585 eq287705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287705 eq330585
  have eq330729 : (k (k (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op (M.op x x) (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq142 eq330586
    | exact resolve eq330586 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq330586
  have eq330771 : (k (k (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op (M.op x x) (k x x))) := by
    first
    | exact superpose eq287609 eq330729
    | exact resolve eq330729 eq287609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330729
  have eq330865 : (k (k (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq330771
       have i₂ := eq46505
       grind)
    | exact superpose eq46505 eq330771
    | exact resolve eq330771 eq46505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46505 eq330771
  have eq330915 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (k (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq330865
       have i₂ := eq289366 (M.op x x) x
       grind)
    | exact superpose eq289366 eq330865
    | exact resolve eq330865 eq289366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289366 eq330865
  have eq330950 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq57663 eq330915
    | exact resolve eq330915 eq57663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57663 eq330915
  have eq331037 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq330950 eq11
    | (have j0 := eq11 (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq11 eq330950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330950
  have eq331061 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by grind
  clear eq331037
  have eq332084 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) = (k X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq331061 eq1929
    | exact resolve eq1929 eq331061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1929 eq331061
  have eq339816 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq316335 eq332084
    | exact resolve eq332084 eq316335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316335 eq332084
  have eq339892 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq57227 eq339816
    | exact resolve eq339816 eq57227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57227
  have eq339903 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq53 eq339816
    | exact resolve eq339816 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339816
  have eq340131 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq287939 eq339892
    | exact resolve eq339892 eq287939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339892
  have eq340161 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq340131
       have r₂ := eq27
       grind)
    | exact resolve eq340131 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340131
  have eq340172 : x = (M.op y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq287609 eq340161
    | exact resolve eq340161 eq287609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340161
  have eq358634 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op (M.op X4 X4) X5) y) = (M.op X0 (M.op X1 (M.op X2 x))) := by
    intro X0 X1 X2 X4 X5
    first
    | exact superpose eq287609 eq1992
    | exact resolve eq1992 eq287609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1992
  have eq358635 : ∀ X0 X4 X5 : G, (M.op (M.op (M.op X4 X4) X5) y) = (M.op X0 (τ (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    intro X0 X4 X5
    first
    | (have i₁ := eq358634 X0 x x X4 X5
       have i₂ := eq289621 x x
       grind)
    | exact superpose eq289621 eq358634
    | exact resolve eq358634 eq289621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289621 eq358634
  have eq359875 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) y) = (M.op X0 (τ (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq4245 X0 y (M.op x x)
       have i₂ := eq358635 X0 x sF4
       grind)
    | exact superpose eq358635 eq4245
    | exact resolve eq4245 eq358635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4245 eq358635
  have eq360495 : ∀ X0 : G, (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op X0 (τ (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq295641 eq359875
    | exact resolve eq359875 eq295641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295641 eq359875
  have eq380355 : ∀ X0 X1 : G, (τ (M.op X0 (M.op (σ x) (σ y)))) = (M.op X1 (τ (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq339903 eq360495
    | exact resolve eq360495 eq339903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339903 eq360495
  have eq502672 : x ≠ x ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq340172
       grind)
    | exact superpose eq340172 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq340172
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq340172
       grind)
    | exact resolve eq13 eq340172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340172
  have eq502761 : (M.op x y) = (k y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq502672
  have eq502801 : (M.op x y) = (k y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq502761
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq502761
    | exact resolve eq502761 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502761
  have eq502815 : x = (k y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq287609 eq502801
    | exact resolve eq502801 eq287609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502801
  have eq515067 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2538 y x
       have i₂ := eq502815
       grind)
    | exact superpose eq502815 eq2538
    | (have j0 := eq2538 y x
       grind)
    | exact resolve eq2538 eq502815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2538 eq502815
  have eq515070 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq515067
  have eq515097 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq515070
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq515070
    | exact resolve eq515070 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515070
  have eq515115 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq515097
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq515097
    | exact resolve eq515097 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515097
  have eq515133 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq515115
    | exact resolve eq515115 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515115
  have eq515152 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq287888 eq515133
    | exact resolve eq515133 eq287888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515133
  have eq515164 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq515152
       have r₂ := eq27
       grind)
    | exact resolve eq515152 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515152
  have eq515173 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq515164
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq515164
    | exact resolve eq515164 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515164
  have eq515187 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq515173
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq515173
    | exact resolve eq515173 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515173
  have eq515195 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq515187
    | exact resolve eq515187 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq515187
  have eq515196 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq515195
  have eq515223 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X0 (σ y)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq515196 eq259
    | exact resolve eq259 eq515196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq515649 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq287939 eq515223
    | (have j0 := eq515223 X0 (σ x)
       grind)
    | exact resolve eq515223 eq287939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515223
  have eq517794 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq53 eq515649
    | exact resolve eq515649 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515649
  have eq518889 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq515196 eq517794
    | exact resolve eq517794 eq515196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515196 eq517794
  have eq519654 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq518889 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518889
  have eq533262 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq53 eq519654
    | exact resolve eq519654 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq519654
  have eq542621 : ∀ X1 : G, (τ (σ y)) = (M.op X1 (τ (σ y))) ∨ x = y := by
    intro X1
    first
    | exact superpose eq533262 eq380355
    | exact resolve eq380355 eq533262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380355 eq533262
  have eq543251 : ∀ X1 : G, y = (M.op X1 y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq29 eq542621
    | exact resolve eq542621 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq542621
  have eq545315 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq543251 x
       grind)
    | exact superpose eq543251 eq18
    | (have j1 := eq543251 x
       grind)
    | exact resolve eq18 eq543251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543251
  have eq545512 : x = y ∨ x = y := by
    first
    | exact superpose eq287609 eq545315
    | exact resolve eq545315 eq287609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545315
  have eq545513 : x = y := by grind
  clear eq545512
  have eq545850 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq545513
       grind)
    | exact superpose eq545513 eq18
    | exact resolve eq18 eq545513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq545851 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq545513
       grind)
    | exact superpose eq545513 eq24
    | exact resolve eq24 eq545513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq545513
  have eq546379 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq545851
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq545851
    | exact resolve eq545851 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq545851
  have eq546380 : x = (M.op x x) := by
    first
    | exact superpose eq287609 eq545850
    | exact resolve eq545850 eq287609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287609 eq545850
  have eq546479 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq287888 eq546379
    | exact resolve eq546379 eq287888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287888 eq546379
  have eq546915 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq546479 eq287939
    | exact resolve eq287939 eq546479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287939 eq546479
  have eq547218 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq546380
       have i₂ := eq287663 X0 x
       grind)
    | (have i₁ := eq546380
       have i₂ := eq287663 x X0
       grind)
    | exact superpose eq287663 eq546380
    | exact resolve eq546380 eq287663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287663 eq546380
  have eq548421 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq290952 x
       have i₂ := eq547218 x
       grind)
    | exact superpose eq547218 eq290952
    | exact resolve eq290952 eq547218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290952 eq547218
  have eq549018 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq546915 eq548421
    | exact resolve eq548421 eq546915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546915 eq548421
  have eq549264 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq549018
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq549018
    | exact resolve eq549018 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq549018
  have eq549415 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq549264
    | exact resolve eq549264 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq549264
  have eq549476 : False := by grind
  exact eq549476
