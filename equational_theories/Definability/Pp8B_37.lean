import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2533`: `x = (y ◇ ((y ◇ x) ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyx_x_pyx_Equation2533 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2533 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2533.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq63 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
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
  have eq64 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) := by
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
  have eq68 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq84 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq84 y x
       grind)
    | exact superpose eq84 eq76
    | (have j1 := eq84 y x
       grind)
    | exact resolve eq76 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq103
    | exact resolve eq103 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq115
  have eq123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq116 eq84
    | (have j0 := eq84 (σ y) (σ x)
       grind)
    | exact resolve eq84 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq123
    | exact resolve eq123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq124
       have r₂ := eq27
       grind)
    | exact resolve eq124 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq129 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq127
    | exact resolve eq127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq143 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129 eq64
    | exact resolve eq64 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq144 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129 eq27
    | exact resolve eq27 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129 eq68
    | (have r₁ := eq68
       have r₂ := eq129
       grind)
    | exact resolve eq68 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq129
  have eq304 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq303
  have eq305 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq304
       have r₂ := eq143
       grind)
    | exact resolve eq304 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq304
  have eq308 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq305 eq116
    | exact resolve eq116 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq305
  have eq312 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq308
  have eq317 : y = (M.op x y) := by
    first
    | (have r₁ := eq312
       have r₂ := eq144
       grind)
    | exact resolve eq312 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq312
  have eq320 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq317 eq20
    | exact resolve eq20 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq323 : x ≠ y ∨ y = (k y x) := by
    first
    | exact superpose eq317 eq63
    | exact resolve eq63 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq324 : y ≠ y ∨ x = y ∨ y = (k y x) := by
    first
    | exact superpose eq317 eq67
    | (have r₁ := eq67
       have r₂ := eq317
       grind)
    | exact resolve eq67 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq317
  have eq329 : x = y ∨ y = (k y x) := by grind
  clear eq324
  have eq335 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq320
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq320
    | exact resolve eq320 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq340 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq335 eq26
    | exact resolve eq26 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq468 : y = (k y x) := by
    first
    | (have r₁ := eq329
       have r₂ := eq323
       grind)
    | exact resolve eq329 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq329
  have eq472 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq468
       grind)
    | exact superpose eq468 eq76
    | exact resolve eq76 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq468
  have eq479 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq335 eq472
    | exact resolve eq472 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq481 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq479
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq479
    | exact resolve eq479 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq479
  have eq482 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq335 eq481
    | exact resolve eq481 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335 eq481
  have eq485 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq482 eq84
    | (have j0 := eq84 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq84 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq482
  have eq486 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq485
  have eq488 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq340 eq486
    | exact resolve eq486 eq340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340 eq486
  have eq491 : False := by grind
  exact eq491

/-- `Equation2533`: `x = (y ◇ ((y ◇ x) ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation2533 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2533 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2533.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
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
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
  have eq48 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq60 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ (M.op X0 X0)) (k X1 (σ X0))
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq97 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq98 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq95
    | (have j0 := eq95 X0 X1
       grind)
    | exact resolve eq95 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq276 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq98 x y
       grind)
    | exact superpose eq98 eq16
    | (have j1 := eq98 x y
       grind)
    | exact resolve eq16 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq98 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq994 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq97
    | exact resolve eq97 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq1037 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq994 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq994
    | (have j0 := eq994 X0 X1
       grind)
    | exact resolve eq994 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994
  have eq1699 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq276
       have i₂ := eq1037 y x
       grind)
    | exact superpose eq1037 eq276
    | (have j1 := eq1037 y x
       grind)
    | (have r₁ := eq276
       have r₂ := eq1037 y x
       grind)
    | (have r₁ := eq276
       have r₂ := eq1037 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq276
       have r₂ := eq1037 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq276 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276 eq1037
  have eq1700 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq1699
  have eq1942 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq280 (τ X1) (τ X0)
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq280
    | (have j0 := eq280 (τ X1) (τ X0)
       grind)
    | exact resolve eq280 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq1974 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1942 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq1942
    | (have j0 := eq1942 X0 X1
       grind)
    | exact resolve eq1942 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1942
  have eq1996 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1974 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1974
    | (have j0 := eq1974 X0 X1
       grind)
    | exact resolve eq1974 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1974
  have eq2015 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1996 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1996
    | (have j0 := eq1996 X0 X1
       grind)
    | exact resolve eq1996 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1996
  have eq2030 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2015 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2015
    | (have j0 := eq2015 X0 X1
       grind)
    | exact resolve eq2015 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2015
  have eq2040 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2030 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq2030
    | (have j0 := eq2030 X0 X1
       grind)
    | exact resolve eq2030 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2030
  have eq2050 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2040 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2040
    | (have j0 := eq2040 X0 X1
       grind)
    | exact resolve eq2040 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040
  have eq2055 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2050 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2050
    | (have j0 := eq2050 X0 X1
       grind)
    | exact resolve eq2050 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2050
  have eq16572 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1700
       grind)
    | exact superpose eq1700 eq16
    | exact resolve eq16 eq1700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1700
  have eq16573 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq16572
       have r₂ := eq22 x
       grind)
    | exact resolve eq16572 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16572
  have eq16663 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq16573
       grind)
    | exact superpose eq16573 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq16573
       grind)
    | exact resolve eq13 eq16573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16573
  have eq16665 : x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq16663
  have eq19008 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16665
       grind)
    | exact superpose eq16665 eq16
    | exact resolve eq16 eq16665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16665
  have eq19009 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq19008
       have r₂ := eq22 x
       grind)
    | exact resolve eq19008 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19008
  have eq19209 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq60 x (σ y)
       have i₂ := eq19009
       grind)
    | exact superpose eq19009 eq60
    | (have j0 := eq60 x (σ y)
       grind)
    | (have r₁ := eq60 x (σ y)
       have r₂ := eq19009
       grind)
    | exact resolve eq60 eq19009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19009
  have eq19226 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by grind
  clear eq19209
  have eq19227 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by grind
  clear eq19226
  have eq19230 : (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq19227
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq19227
    | exact resolve eq19227 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19227
  have eq19561 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq280 x y
       have i₂ := eq19230
       grind)
    | exact superpose eq19230 eq280
    | (have j0 := eq280 x y
       grind)
    | (have r₁ := eq280 x y
       have r₂ := eq19230
       grind)
    | exact resolve eq280 eq19230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19230
  have eq19588 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq19561
  have eq19589 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq19588
  have eq19595 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq280 x y
       grind)
    | (have r₁ := eq19589
       have r₂ := eq280 x y
       grind)
    | exact resolve eq19589 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280 eq19589
  have eq19600 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19595
       grind)
    | exact superpose eq19595 eq16
    | exact resolve eq16 eq19595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19601 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq60 x (σ y)
       have i₂ := eq19595
       grind)
    | exact superpose eq19595 eq60
    | (have j0 := eq60 x (σ y)
       grind)
    | (have r₁ := eq60 x (σ y)
       have r₂ := eq19595
       grind)
    | exact resolve eq60 eq19595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq19595
  have eq19618 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq19601
  have eq19619 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq19618
  have eq19622 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq19619
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq19619
    | exact resolve eq19619 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19619
  have eq19952 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq19622
       grind)
    | exact superpose eq19622 eq10
    | exact resolve eq10 eq19622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19622
  have eq20129 : x = y ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq19952
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19952
    | exact resolve eq19952 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19952
  have eq20278 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20129
       grind)
    | exact superpose eq20129 eq16
    | exact resolve eq16 eq20129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20129
  have eq20279 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq20278
       have r₂ := eq22 x
       grind)
    | exact resolve eq20278 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20278
  have eq20294 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq20279
       grind)
    | exact superpose eq20279 eq10
    | exact resolve eq10 eq20279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20279
  have eq20473 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq20294
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq20294
    | exact resolve eq20294 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20294
  have eq20885 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq2055 y x
       have i₂ := eq20473
       grind)
    | exact superpose eq20473 eq2055
    | (have j0 := eq2055 y x
       grind)
    | (have r₁ := eq2055 y x
       have r₂ := eq20473
       grind)
    | exact resolve eq2055 eq20473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2055 eq20473
  have eq20905 : (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq20885
  have eq20909 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq19600
       have i₂ := eq20905
       grind)
    | exact superpose eq20905 eq19600
    | exact resolve eq19600 eq20905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19600 eq20905
  have eq20919 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq20909
  have eq21257 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20919
       grind)
    | exact superpose eq20919 eq16
    | exact resolve eq16 eq20919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20919
  have eq21260 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq21257
       have r₂ := eq22 x
       grind)
    | exact resolve eq21257 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21257
  have eq21261 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21260
       grind)
    | exact superpose eq21260 eq16
    | exact resolve eq16 eq21260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21262 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq21260
       grind)
    | exact superpose eq21260 eq10
    | exact resolve eq10 eq21260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21260
  have eq21440 : x = y := by
    first
    | (have i₁ := eq21262
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq21262
    | exact resolve eq21262 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21262
  have eq21441 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq21261
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq21261
    | exact resolve eq21261 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq21261
  have eq21442 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq21441
       have i₂ := eq21440
       grind)
    | exact superpose eq21440 eq21441
    | exact resolve eq21441 eq21440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21440 eq21441
  have eq21443 : False := by grind
  exact eq21443

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyx_pyy_pxx_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq77 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       have j1 := eq72 X1 X0
       grind)
    | (have r₁ := eq74 X1 X0
       have r₂ := eq72 X0 X1
       grind)
    | (have r₁ := eq74 X0 (M.op X1 X1)
       have r₂ := eq72 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq74 X1 X1
       have r₂ := eq72 (k X1 X1) X1
       grind)
    | exact resolve eq74 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq74
  have eq107 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq23 X0 X1 X2 X3
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq23 X0 X1 X2 X3
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq116 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq116
    | exact resolve eq116 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq121 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq107 X0 x x X3 X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq107
    | exact resolve eq107 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq128 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq120 X0 X1
       grind)
    | exact superpose eq120 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq335 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq328 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq328 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq328 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq328 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq328 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq357 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq335 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq335
    | (have j0 := eq335 (σ X0) (σ X1)
       grind)
    | exact resolve eq335 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq357 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq389 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq378 y x
       grind)
    | exact superpose eq378 eq16
    | (have j1 := eq378 y x
       grind)
    | exact resolve eq16 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq378 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq479 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0 X0 x X0
       have i₂ := eq121 X0 X0 x
       grind)
    | exact superpose eq121 eq23
    | exact resolve eq23 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq518 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq121 X0 X0 X0
       have i₂ := eq479 X0
       grind)
    | exact superpose eq479 eq121
    | exact resolve eq121 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq519 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X0 X0 X1
       have i₂ := eq479 X0
       grind)
    | exact superpose eq479 eq23
    | exact resolve eq23 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq479
  have eq540 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq404 (τ X1) (τ X0)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq404
    | (have j0 := eq404 (τ X1) (τ X0)
       grind)
    | exact resolve eq404 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq547 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq540 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq540
    | (have j0 := eq540 X0 X1
       grind)
    | exact resolve eq540 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq549 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq547 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq547
    | (have j0 := eq547 X0 X1
       grind)
    | exact resolve eq547 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq550 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq549 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq549
    | (have j0 := eq549 X0 X1
       grind)
    | exact resolve eq549 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq551 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq550 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq550
    | (have j0 := eq550 X0 X1
       grind)
    | exact resolve eq550 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq588 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq128 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq518 X0
       grind)
    | exact superpose eq518 eq128
    | (have r₁ := eq128 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq518 X0
       grind)
    | exact resolve eq128 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq596 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq588 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq651 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq389
       have i₂ := eq335 y x
       grind)
    | exact superpose eq335 eq389
    | (have j1 := eq335 (σ y) (σ x)
       grind)
    | exact resolve eq389 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335 eq389
  have eq655 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq651
  have eq799 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq120 (σ x) (σ y)
       have i₂ := eq655
       grind)
    | exact superpose eq655 eq120
    | exact resolve eq120 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq831 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128 (σ x) (σ x)
       have i₂ := eq799
       grind)
    | exact superpose eq799 eq128
    | (have r₁ := eq128 (σ x) (σ x)
       have r₂ := eq799
       grind)
    | (have r₁ := eq128 x y
       have r₂ := eq799
       grind)
    | exact resolve eq128 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq799
  have eq843 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq831
  have eq847 : (σ x) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq843
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq843
    | exact resolve eq843 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq863 : (k x x) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq847
       grind)
    | exact superpose eq847 eq10
    | exact resolve eq10 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq891 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq863
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq863
    | exact resolve eq863 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq1037 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq551 x x
       have i₂ := eq891
       grind)
    | exact superpose eq891 eq551
    | (have j0 := eq551 x x
       grind)
    | (have r₁ := eq551 x x
       have r₂ := eq891
       grind)
    | exact resolve eq551 eq891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551 eq891
  have eq1038 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq1037
  have eq1059 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq120 x y
       have i₂ := eq1038
       grind)
    | exact superpose eq1038 eq120
    | exact resolve eq120 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038
  have eq1064 : x = (M.op x x) := by grind
  clear eq1059
  have eq1118 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq519 x X0
       have i₂ := eq1064
       grind)
    | exact superpose eq1064 eq519
    | exact resolve eq519 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq1119 : x = (k x x) := by
    first
    | (have i₁ := eq596 x
       have i₂ := eq1064
       grind)
    | exact superpose eq1064 eq596
    | exact resolve eq596 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq1123 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq1118 X0
       have i₂ := eq120 x X0
       grind)
    | (have i₁ := eq1118 X0
       have i₂ := eq120 x (M.op x X0)
       grind)
    | exact superpose eq120 eq1118
    | exact resolve eq1118 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq1118
  have eq1440 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq404 x x
       have i₂ := eq1119
       grind)
    | exact superpose eq1119 eq404
    | (have j0 := eq404 x x
       grind)
    | exact resolve eq404 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404 eq1119
  have eq1443 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1440
  have eq1462 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq1123 X0
       grind)
    | exact superpose eq1123 eq9
    | exact resolve eq9 eq1123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123
  have eq1483 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1462 X0
       have i₂ := eq1064
       grind)
    | exact superpose eq1064 eq1462
    | exact resolve eq1462 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064 eq1462
  have eq1527 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x X1
       have i₂ := eq1483 (M.op (M.op x X0) X1)
       grind)
    | exact superpose eq1483 eq9
    | exact resolve eq9 eq1483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1531 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1527 X0 X1
       have i₂ := eq1483 X0
       grind)
    | exact superpose eq1483 eq1527
    | exact resolve eq1527 eq1483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1527
  have eq1654 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 X0
       have i₂ := eq1531 X0 X1
       grind)
    | exact superpose eq1531 eq9
    | exact resolve eq9 eq1531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1531
  have eq2056 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1654 (σ x) X0
       have i₂ := eq1443
       grind)
    | exact superpose eq1443 eq1654
    | exact resolve eq1654 eq1443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1443 eq1654
  have eq2101 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2056 (σ y)
       grind)
    | exact superpose eq2056 eq16
    | exact resolve eq16 eq2056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2056
  have eq2167 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2101
       have i₂ := eq1483 y
       grind)
    | exact superpose eq1483 eq2101
    | exact resolve eq2101 eq1483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1483 eq2101
  have eq2168 : False := by grind
  exact eq2168

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyy_pxy_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : x ≠ (M.op x y) ∨ (k y x) = (M.op x x) := by
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
  have eq64 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
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
  clear eq36
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
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
  have eq92 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq87
    | exact resolve eq87 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq93
    | exact resolve eq93 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94
    | exact resolve eq94 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq95
    | exact resolve eq95 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq110 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq110 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq110 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq110 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq114 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq111 x
       grind)
    | exact superpose eq111 eq43
    | exact resolve eq43 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq111 sF2
       grind)
    | exact superpose eq111 eq49
    | exact resolve eq49 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq117 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq116
       have i₂ := eq111 x
       grind)
    | exact superpose eq111 eq116
    | exact resolve eq116 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq119 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq114
       have i₂ := eq111 sF2
       grind)
    | exact superpose eq111 eq114
    | exact resolve eq114 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq169 : (σ (k (k x x) x)) = (k (k (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq39 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq39
    | exact resolve eq39 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ X0) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq183 : (σ (k (k x x) x)) = (k (M.op (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq169
       have i₂ := eq111 sF2
       grind)
    | exact superpose eq111 eq169
    | exact resolve eq169 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq185 : (k (M.op (σ x) (σ x)) (σ x)) = (σ (k (M.op x x) x)) := by
    first
    | (have i₁ := eq183
       have i₂ := eq111 x
       grind)
    | exact superpose eq111 eq183
    | exact resolve eq183 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq305 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq111 (τ X0)
       grind)
    | exact superpose eq111 eq34
    | exact resolve eq34 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq316 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq305 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq305
    | exact resolve eq305 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq318 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq316 X0
       have i₂ := eq111 X0
       grind)
    | exact superpose eq111 eq316
    | exact resolve eq316 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq540 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq557 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq552 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq552
    | exact resolve eq552 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq560 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq540 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq540
    | exact resolve eq540 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq567 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq557 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq557
    | (have j0 := eq557 x y
       grind)
    | exact resolve eq557 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq569 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq557
    | (have j0 := eq557 (σ x) (σ y)
       grind)
    | exact resolve eq557 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq582 : ∀ X0 : G, (M.op x y) = (M.op (M.op x (M.op (M.op x y) X0)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq567 eq14
    | exact resolve eq14 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq854 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq318 X0
       grind)
    | exact superpose eq318 eq16
    | exact resolve eq16 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq1028 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq557 (τ X0) (τ X0)
       have i₂ := eq854 X0
       grind)
    | exact superpose eq854 eq557
    | exact resolve eq557 eq854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq4052 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 X0 x X0
       have i₂ := eq560 X0 X0 x
       grind)
    | exact superpose eq560 eq52
    | exact resolve eq52 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq560
  have eq5416 : (σ (k (k x x) x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (M.op (σ x) (k (σ x) (σ x))) = (M.op (k (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq180 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq180
    | exact resolve eq180 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq180
  have eq5481 : (σ (k (k x x) x)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (M.op (σ x) (k (σ x) (σ x))) = (M.op (k (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq5416
       have i₂ := eq111 sF2
       grind)
    | exact superpose eq111 eq5416
    | exact resolve eq5416 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5416
  have eq5494 : (M.op (σ x) (σ x)) = (σ (k (k x x) x)) ∨ (M.op (σ x) (k (σ x) (σ x))) = (M.op (k (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq5481
       have i₂ := eq557 sF2 (M.op sF2 sF2)
       grind)
    | (have i₁ := eq5481
       have i₂ := eq557 sF2 sF2
       grind)
    | exact superpose eq557 eq5481
    | exact resolve eq5481 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5481
  have eq5500 : (M.op (σ x) (σ x)) = (σ (k (M.op x x) x)) ∨ (M.op (σ x) (k (σ x) (σ x))) = (M.op (k (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq5494
       have i₂ := eq111 x
       grind)
    | exact superpose eq111 eq5494
    | exact resolve eq5494 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5494
  have eq5504 : (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (M.op (σ x) (k (σ x) (σ x))) = (M.op (k (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq5500
       have i₂ := eq185
       grind)
    | exact superpose eq185 eq5500
    | exact resolve eq5500 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq5500
  have eq5507 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq5504
       have i₂ := eq111 sF2
       grind)
    | exact superpose eq111 eq5504
    | exact resolve eq5504 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5504
  have eq5509 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq5507
       have i₂ := eq4052 sF2
       grind)
    | exact superpose eq4052 eq5507
    | exact resolve eq5507 eq4052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4052 eq5507
  have eq5510 : (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (k (σ x) (σ x))) := by
    first
    | (have j1 := eq13 (M.op (σ x) (σ x)) (σ x)
       grind)
    | (have r₁ := eq5509
       have r₂ := eq13 (M.op (σ x) (σ x)) (σ x)
       grind)
    | (have r₁ := eq5509
       have r₂ := eq13 (k (σ x) (σ x)) (σ x)
       grind)
    | exact resolve eq5509 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5509
  have eq5511 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq5510
       have i₂ := eq111 sF2
       grind)
    | exact superpose eq111 eq5510
    | exact resolve eq5510 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq5510
  have eq5512 : (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ x)) (σ x)) := by
    first
    | (have j1 := eq13 (M.op (σ x) (σ x)) (σ x)
       grind)
    | (have r₁ := eq5511
       have r₂ := eq13 (M.op (σ x) (σ x)) (σ x)
       grind)
    | exact resolve eq5511 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5511
  have eq11575 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11576 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq11575
    | exact resolve eq11575 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11575
  have eq11587 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11576
       have r₂ := eq27
       grind)
    | exact resolve eq11576 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11576
  have eq11591 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq11587
    | exact resolve eq11587 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11587
  have eq11593 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq11591
    | exact resolve eq11591 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11591
  have eq11601 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11593 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq11593
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq11593
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11593
       grind)
    | exact resolve eq12 eq11593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11593
  have eq11623 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11601
       have r₂ := eq26
       grind)
    | exact resolve eq11601 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11601
  have eq11628 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq11623
    | exact resolve eq11623 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11623
  have eq11629 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq11628
  have eq11730 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11629 eq96
    | exact resolve eq96 eq11629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq11629
  have eq11738 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11730
  have eq11740 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11738
       have r₂ := eq27
       grind)
    | exact resolve eq11738 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11738
  have eq11978 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq11740
       grind)
    | exact superpose eq11740 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11740
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq11740
       grind)
    | exact resolve eq12 eq11740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11740
  have eq12002 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11978
       have r₂ := eq18
       grind)
    | exact resolve eq11978 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11978
  have eq12008 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12002
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12002
    | exact resolve eq12002 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12002
  have eq12009 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12008
  have eq12104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq12009
       grind)
    | exact superpose eq12009 eq72
    | exact resolve eq72 eq12009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12009
  have eq12118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq12104
    | exact resolve eq12104 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12104
  have eq12526 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12118 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq12118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12529 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12526
    | exact resolve eq12526 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12526
  have eq12540 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12529
       have r₂ := eq27
       grind)
    | exact resolve eq12529 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12529
  have eq12544 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12540
    | exact resolve eq12540 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12540
  have eq12546 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12544
    | exact resolve eq12544 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12544
  have eq12547 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12546
  have eq12979 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12547 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq12547
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq12547
       grind)
    | exact resolve eq12 eq12547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12547
  have eq13008 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12979
       have r₂ := eq26
       grind)
    | exact resolve eq12979 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12979
  have eq13014 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq13008
    | exact resolve eq13008 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13008
  have eq13015 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13014
  have eq13132 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13015 eq12118
    | exact resolve eq12118 eq13015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12118 eq13015
  have eq13134 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13132
  have eq13138 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13134
       have r₂ := eq27
       grind)
    | exact resolve eq13134 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13134
  have eq13141 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13138 eq51
    | exact resolve eq51 eq13138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq13142 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13138 eq64
    | (have r₁ := eq64
       have r₂ := eq13138
       grind)
    | exact resolve eq64 eq13138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq13151 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13138 eq569
    | exact resolve eq569 eq13138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq13163 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq13142
  have eq13174 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13141 X0
       have i₂ := eq557 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq13141 x
       have i₂ := eq557 sF2 x
       grind)
    | exact superpose eq557 eq13141
    | exact resolve eq13141 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13141
  have eq13889 : (k y x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13163 eq92
    | exact resolve eq92 eq13163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq13163
  have eq13916 : (k y x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq117 eq13889
    | exact resolve eq13889 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq13889
  have eq13920 : (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq13916
       have r₂ := eq63
       grind)
    | exact resolve eq13916 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq13916
  have eq13926 : (k (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq13920
       grind)
    | exact superpose eq13920 eq72
    | exact resolve eq72 eq13920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq13920
  have eq13942 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq13926
       have i₂ := eq119
       grind)
    | exact superpose eq119 eq13926
    | exact resolve eq13926 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13926
  have eq14056 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13151 eq13174
    | exact resolve eq13174 eq13151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13151 eq13174
  have eq14115 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14056
  have eq14135 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq14115
    | exact resolve eq14115 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14115
  have eq14172 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14135 eq13138
    | exact resolve eq13138 eq14135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13138
  have eq14175 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq14172
  have eq14323 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14175 eq26
    | exact resolve eq26 eq14175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14324 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14175 eq29
    | exact resolve eq29 eq14175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14175
  have eq14463 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq14324
    | exact resolve eq14324 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14324
  have eq16005 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14323 eq5512
    | exact resolve eq5512 eq14323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5512 eq14323
  have eq17071 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14135 eq16005
    | exact resolve eq16005 eq14135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14135 eq16005
  have eq17077 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq17071
  have eq17079 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13942 eq17077
    | exact resolve eq17077 eq13942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13942 eq17077
  have eq17354 : (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17079 eq1028
    | exact resolve eq1028 eq17079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028 eq17079
  have eq17413 : y = (M.op (τ (σ x)) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq17354
    | exact resolve eq17354 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17354
  have eq17424 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq17413
    | exact resolve eq17413 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq17413
  have eq17427 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17424
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17424
    | exact resolve eq17424 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17424
  have eq17508 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq17427
  have eq17510 : x = (M.op x y) := by
    first
    | (have r₁ := eq17508
       have r₂ := eq14463
       grind)
    | exact resolve eq17508 eq14463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14463 eq17508
  have eq17600 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq17510 eq20
    | exact resolve eq20 eq17510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq17660 : x = (M.op x x) := by
    first
    | exact superpose eq17510 eq567
    | exact resolve eq567 eq17510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq17662 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | exact superpose eq17510 eq582
    | exact resolve eq582 eq17510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq17681 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq17662 X0
       have i₂ := eq557 x X0
       grind)
    | (have i₁ := eq17662 X0
       have i₂ := eq557 x (M.op x X0)
       grind)
    | exact superpose eq557 eq17662
    | exact resolve eq17662 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq17662
  have eq17738 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq17600
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17600
    | exact resolve eq17600 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17600
  have eq17781 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq17738 eq26
    | exact resolve eq26 eq17738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq17986 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq119
       have i₂ := eq17660
       grind)
    | exact superpose eq17660 eq119
    | exact resolve eq119 eq17660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq18081 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq17738 eq17986
    | exact resolve eq17986 eq17738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17986
  have eq18106 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq18081
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18081
    | exact resolve eq18081 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18081
  have eq18120 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq17738 eq18106
    | exact resolve eq18106 eq17738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18106
  have eq18359 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq17681 X0
       grind)
    | exact superpose eq17681 eq14
    | exact resolve eq14 eq17681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17681
  have eq18431 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18359 X0
       have i₂ := eq17660
       grind)
    | exact superpose eq17660 eq18359
    | exact resolve eq18359 eq17660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17660 eq18359
  have eq18472 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq18431 y
       grind)
    | exact superpose eq18431 eq18
    | (have j1 := eq18431 y
       grind)
    | exact resolve eq18 eq18431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq18431
  have eq18602 : x = y := by
    first
    | exact superpose eq17510 eq18472
    | exact resolve eq18472 eq17510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17510 eq18472
  have eq18727 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq18602
       grind)
    | exact superpose eq18602 eq24
    | exact resolve eq24 eq18602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq18602
  have eq18852 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq18727
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18727
    | exact resolve eq18727 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq18727
  have eq18910 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq17738 eq18852
    | exact resolve eq18852 eq17738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17738 eq18852
  have eq19192 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq18910 eq17781
    | exact resolve eq17781 eq18910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17781 eq18910
  have eq19194 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18120 eq19192
    | exact resolve eq19192 eq18120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18120 eq19192
  have eq19259 : False := by grind
  exact eq19259

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pyy_x_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X0) X2)) ≠ X0 ∨ (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X1 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       grind)
    | exact resolve eq13 eq14
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
  clear eq36
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq108
    | exact resolve eq108 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq167 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq455 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq52 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x X0 X1 y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq466 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq466 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq466
    | exact resolve eq466 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq472 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq455 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq455
    | exact resolve eq455 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq478 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq469 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq469
    | (have j0 := eq469 x y
       grind)
    | exact resolve eq469 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq469
    | (have j0 := eq469 (σ x) (σ y)
       grind)
    | exact resolve eq469 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq496 : ∀ X0 : G, (M.op x y) = (M.op (M.op x (M.op (M.op x y) X0)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq478 eq14
    | exact resolve eq14 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq598 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq90 X1 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq13 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq601 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq90 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq603 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq601 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq606 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq598 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq598 X0 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq598 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq598 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq615 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq606 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq606
    | (have j0 := eq606 X0 X1
       grind)
    | exact resolve eq606 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq728 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) ≠ X0 ∨ (k X0 (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4))) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq65 X0 (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X2
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq65
    | exact resolve eq65 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) ≠ (M.op X0 X3) ∨ (k (M.op X0 X3) (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0)) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq65 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq65
    | exact resolve eq65 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq751 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) ≠ X0 ∨ (k (M.op X0 X3) (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0)) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq741 X0 X1 X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq741
    | (have j0 := eq741 X0 X1 X2 X3
       grind)
    | exact resolve eq741 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq756 : ∀ X0 X3 : G, (M.op X0 X3) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X3) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq751 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq751
    | (have j0 := eq751 X0 x x X3
       grind)
    | exact resolve eq751 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq3250 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 X0 x X0
       have i₂ := eq472 X0 X0 x
       grind)
    | exact superpose eq472 eq52
    | exact resolve eq52 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3289 : x = (M.op (M.op (M.op x x) (M.op x y)) x) := by
    first
    | (have i₁ := eq462 x x
       have i₂ := eq3250 x
       grind)
    | exact superpose eq3250 eq462
    | exact resolve eq462 eq3250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq3290 : (σ x) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq464 sF2 sF2
       have i₂ := eq3250 sF2
       grind)
    | exact superpose eq3250 eq464
    | exact resolve eq464 eq3250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq3291 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq472 X0 X0 X0
       have i₂ := eq3250 X0
       grind)
    | exact superpose eq3250 eq472
    | exact resolve eq472 eq3250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472 eq3250
  have eq3348 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq603 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq603
    | (have j0 := eq603 (τ X0)
       grind)
    | exact resolve eq603 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq603
  have eq3356 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3348 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3348
    | (have j0 := eq3348 X0
       grind)
    | exact resolve eq3348 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3348
  have eq3362 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3356 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3356
    | (have j0 := eq3356 X0
       grind)
    | exact resolve eq3356 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3356
  have eq3713 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq756 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq3291 X0
       grind)
    | exact superpose eq3291 eq756
    | (have r₁ := eq756 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq3291 X0
       grind)
    | exact resolve eq756 eq3291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3291
  have eq3715 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq3713 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3713
  have eq3830 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq167 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq167
    | (have j0 := eq167 x
       grind)
    | exact resolve eq167 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq3846 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3830
  have eq3851 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3846
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq3846
    | exact resolve eq3846 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq3846
  have eq3868 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq3851
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq3851 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3851
  have eq3874 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3868 eq49
    | exact resolve eq49 eq3868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq3868
  have eq14996 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq110 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq15003 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq14996
    | exact resolve eq14996 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14996
  have eq15014 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq15003
       have r₂ := eq27
       grind)
    | exact resolve eq15003 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15003
  have eq15016 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq15014
    | exact resolve eq15014 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15014
  have eq15019 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq15016 eq3874
    | exact resolve eq3874 eq15016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15016
  have eq15090 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq15019
    | exact resolve eq15019 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15019
  have eq15102 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq3362 x
       grind)
    | (have r₁ := eq15090
       have r₂ := eq3362 x
       grind)
    | exact resolve eq15090 eq3362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3362 eq15090
  have eq15105 : x = (M.op (M.op x (M.op x y)) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3289
       have i₂ := eq15102
       grind)
    | exact superpose eq15102 eq3289
    | exact resolve eq3289 eq15102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3289
  have eq15107 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3715 x
       have i₂ := eq15102
       grind)
    | exact superpose eq15102 eq3715
    | exact resolve eq3715 eq15102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15161 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq478 eq15105
    | exact resolve eq15105 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15105
  have eq15190 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq615 x x
       have i₂ := eq15107
       grind)
    | exact superpose eq15107 eq615
    | (have j0 := eq615 x x
       grind)
    | exact resolve eq615 eq15107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15107
  have eq15193 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15190
  have eq15194 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15193
  have eq15206 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15194
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15194
    | exact resolve eq15194 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15194
  have eq15374 : y = (M.op (M.op x x) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15161 eq50
    | exact resolve eq50 eq15161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq15161
  have eq15544 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15206 eq3290
    | exact resolve eq3290 eq15206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3290
  have eq15617 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq480 eq15544
    | exact resolve eq15544 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15544
  have eq15763 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15617 eq51
    | exact resolve eq51 eq15617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15617
  have eq16036 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15374
       have i₂ := eq15102
       grind)
    | exact superpose eq15102 eq15374
    | exact resolve eq15374 eq15102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15102 eq15374
  have eq16072 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16036
  have eq16086 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16072
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16072
    | exact resolve eq16072 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16072
  have eq16090 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16086 eq51
    | exact resolve eq51 eq16086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16091 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16086 eq64
    | (have r₁ := eq64
       have r₂ := eq16086
       grind)
    | exact resolve eq64 eq16086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq16099 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16086 eq480
    | exact resolve eq480 eq16086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16110 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq16091
  have eq16119 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16090 X0
       have i₂ := eq469 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq16090 x
       have i₂ := eq469 sF2 x
       grind)
    | exact superpose eq469 eq16090
    | exact resolve eq16090 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16090
  have eq16124 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16099 eq3874
    | exact resolve eq3874 eq16099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16195 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq16124
    | exact resolve eq16124 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq16124
  have eq16223 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq16195
       grind)
    | exact superpose eq16195 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq16195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16195
  have eq16238 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq16223
  have eq16352 : ∀ X0 X1 X2 : G, x ≠ (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x X2)) x) ∨ (k x (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x X2)) x)) = (M.op (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x X2)) x) (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x X2)) x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq728 x X1 X2 x x
       have i₂ := eq16238
       grind)
    | exact superpose eq16238 eq728
    | exact resolve eq728 eq16238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728 eq16238
  have eq16360 : ∀ X0 X1 X2 : G, (k x (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x X2)) x)) = (M.op (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x X2)) x) (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x X2)) x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have j0 := eq16352 X0 X1 X2
       grind)
    | (have r₁ := eq16352 X1 X2 x
       have r₂ := eq52 x X1 X2 x
       grind)
    | exact resolve eq16352 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16352
  have eq16383 : (k x x) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16360 x x x
       have i₂ := eq52 x x x x
       grind)
    | exact superpose eq52 eq16360
    | exact resolve eq16360 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq16360
  have eq16800 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15206 eq15763
    | exact resolve eq15763 eq15206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15206 eq15763
  have eq16838 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16800
  have eq16853 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16838
    | exact resolve eq16838 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16838
  have eq16856 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16853 eq27
    | exact resolve eq27 eq16853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16853
  have eq17033 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16099 eq16119
    | exact resolve eq16119 eq16099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16099 eq16119
  have eq17087 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq17033
  have eq17105 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq17087
    | exact resolve eq17087 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17087
  have eq17132 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17105 eq16086
    | exact resolve eq16086 eq17105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17135 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq17132
  have eq17141 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17135 eq26
    | exact resolve eq26 eq17135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17135
  have eq18191 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17141 eq756
    | (have j0 := eq756 (σ x) (σ y)
       grind)
    | (have r₁ := eq756 x y
       have r₂ := eq17141
       grind)
    | exact resolve eq756 eq17141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756 eq17141
  have eq18206 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq18191
       have r₂ := eq16086
       grind)
    | exact resolve eq18191 eq16086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16086 eq18191
  have eq18529 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17105 eq18206
    | exact resolve eq18206 eq17105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17105 eq18206
  have eq18542 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18529
  have eq18672 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18542 eq16110
    | exact resolve eq16110 eq18542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16110 eq18542
  have eq18680 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18672
  have eq18944 : (τ (σ y)) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18680 eq3874
    | exact resolve eq3874 eq18680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3874 eq18680
  have eq19023 : y = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq18944
    | exact resolve eq18944 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18944
  have eq22984 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19023
       have i₂ := eq16383
       grind)
    | exact superpose eq16383 eq19023
    | exact resolve eq19023 eq16383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16383 eq19023
  have eq22999 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq22984
  have eq23079 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq469 x x
       have i₂ := eq22999
       grind)
    | exact superpose eq22999 eq469
    | exact resolve eq469 eq22999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22999
  have eq23102 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23079
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23079
    | exact resolve eq23079 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23079
  have eq23103 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq23102
  have eq23105 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23103 eq20
    | exact resolve eq20 eq23103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23103
  have eq23251 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23105
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23105
    | exact resolve eq23105 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23105
  have eq23361 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23251 eq16856
    | (have r₁ := eq16856
       have r₂ := eq23251
       grind)
    | exact resolve eq16856 eq23251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16856
  have eq23389 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23361
  have eq23390 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq23389
  have eq23466 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23390 eq51
    | exact resolve eq51 eq23390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq23475 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23390 eq480
    | exact resolve eq480 eq23390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480 eq23390
  have eq23530 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23466 X0
       have i₂ := eq469 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq23466 x
       have i₂ := eq469 sF2 x
       grind)
    | exact superpose eq469 eq23466
    | exact resolve eq23466 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23466
  have eq26366 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23475 eq23530
    | exact resolve eq23530 eq23475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23475 eq23530
  have eq26430 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq26366
  have eq26459 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq26430
    | exact resolve eq26430 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26430
  have eq26469 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26459 eq27
    | exact resolve eq27 eq26459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26459
  have eq26541 : x = (M.op x y) := by
    first
    | (have r₁ := eq26469
       have r₂ := eq23251
       grind)
    | exact resolve eq26469 eq23251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23251 eq26469
  have eq26545 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq26541 eq20
    | exact resolve eq20 eq26541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq26609 : x = (M.op x x) := by
    first
    | exact superpose eq26541 eq478
    | exact resolve eq478 eq26541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq26611 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | exact superpose eq26541 eq496
    | exact resolve eq496 eq26541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq26634 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq26611 X0
       have i₂ := eq469 x X0
       grind)
    | (have i₁ := eq26611 X0
       have i₂ := eq469 x (M.op x X0)
       grind)
    | exact superpose eq469 eq26611
    | exact resolve eq26611 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469 eq26611
  have eq26695 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq26545
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26545
    | exact resolve eq26545 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26545
  have eq26934 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26695 eq26
    | exact resolve eq26 eq26695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq27138 : x = (k x x) := by
    first
    | (have i₁ := eq3715 x
       have i₂ := eq26609
       grind)
    | exact superpose eq26609 eq3715
    | exact resolve eq3715 eq26609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3715
  have eq27296 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq615 x x
       have i₂ := eq27138
       grind)
    | exact superpose eq27138 eq615
    | (have j0 := eq615 x x
       grind)
    | exact resolve eq615 eq27138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615 eq27138
  have eq27299 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq27296
  have eq27300 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq27299
  have eq27312 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq27300
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27300
    | exact resolve eq27300 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27300
  have eq27328 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26695 eq27312
    | exact resolve eq27312 eq26695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27312
  have eq28229 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq26634 X0
       grind)
    | exact superpose eq26634 eq14
    | exact resolve eq14 eq26634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26634
  have eq28287 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq28229 X0
       have i₂ := eq26609
       grind)
    | exact superpose eq26609 eq28229
    | exact resolve eq28229 eq26609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26609 eq28229
  have eq28321 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28287 y
       grind)
    | exact superpose eq28287 eq18
    | (have j1 := eq28287 y
       grind)
    | exact resolve eq18 eq28287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq28287
  have eq28423 : x = y := by
    first
    | exact superpose eq26541 eq28321
    | exact resolve eq28321 eq26541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26541 eq28321
  have eq28470 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq28423
       grind)
    | exact superpose eq28423 eq24
    | exact resolve eq24 eq28423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq28423
  have eq28618 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq28470
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28470
    | exact resolve eq28470 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq28470
  have eq28684 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26695 eq28618
    | exact resolve eq28618 eq26695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26695 eq28618
  have eq29021 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq28684 eq26934
    | exact resolve eq26934 eq28684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26934 eq28684
  have eq29026 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27328 eq29021
    | exact resolve eq29021 eq27328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27328 eq29021
  have eq29092 : False := by grind
  exact eq29092

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_x_x_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq57 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq80 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq128 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq143 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq148 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq128 eq16
    | exact resolve eq16 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq345 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq58 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3 X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) (M.op X0 X5)) X0) = X0 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq58 X0 (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X4 X5
       have i₂ := eq58 X0 X1 X2 X3
       grind)
    | exact superpose eq58 eq58
    | exact resolve eq58 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq58 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq58 X0 X1 X2 X3
       grind)
    | exact superpose eq58 eq58
    | exact resolve eq58 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq58 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq58
    | (have j0 := eq58 x X0 X1 y
       grind)
    | exact resolve eq58 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq58
    | (have j0 := eq58 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq58 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq58 X0 X1 X2 X3
       grind)
    | exact superpose eq58 eq14
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq359 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq359
    | exact resolve eq359 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq365 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq350 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq350
    | exact resolve eq350 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq383 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq362 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq362
    | (have j0 := eq362 x y
       grind)
    | exact resolve eq362 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq362
    | (have j0 := eq362 (σ x) (σ y)
       grind)
    | exact resolve eq362 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq401 : x ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq383 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq92 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq512 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq510 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq3637 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq58 X0 X0 x X0
       have i₂ := eq365 X0 X0 x
       grind)
    | exact superpose eq365 eq58
    | exact resolve eq58 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq3672 : x = (M.op (M.op (M.op x x) (M.op x y)) x) := by
    first
    | (have i₁ := eq353 x x
       have i₂ := eq3637 x
       grind)
    | exact superpose eq3637 eq353
    | exact resolve eq353 eq3637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3673 : (σ x) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq354 sF2 sF2
       have i₂ := eq3637 sF2
       grind)
    | exact superpose eq3637 eq354
    | exact resolve eq354 eq3637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq3674 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq365 X0 X0 X0
       have i₂ := eq3637 X0
       grind)
    | exact superpose eq3637 eq365
    | exact resolve eq365 eq3637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4476 : ∀ X0 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X2)) X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq345 X0 X0 x X0 X2
       have i₂ := eq365 X0 X0 x
       grind)
    | exact superpose eq365 eq345
    | exact resolve eq345 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq365
  have eq4928 : ∀ X0 : G, (σ x) ≠ (σ (k X0 x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq143 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq5198 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq67 X1 (M.op X0 X0)
       have i₂ := eq3674 X0
       grind)
    | exact superpose eq3674 eq67
    | (have j0 := eq67 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq67 X0 (M.op X0 X0)
       have r₂ := eq3674 X0
       grind)
    | exact resolve eq67 eq3674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3674
  have eq5213 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5198 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5198
  have eq5255 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq331 X0 (M.op X1 X1)
       have i₂ := eq5213 X1 (σ X0)
       grind)
    | exact superpose eq5213 eq331
    | exact resolve eq331 eq5213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331 eq5213
  have eq5261 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5255 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq5255
    | exact resolve eq5255 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5255
  have eq5971 : ∀ X0 X1 X2 X3 X4 : G, (M.op x y) = (M.op (M.op (M.op (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) x) (M.op (M.op x y) X2)) (M.op (M.op x y) X3)) (M.op (M.op x y) X4)) (M.op x y)) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq353 eq346
    | exact resolve eq346 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq353
  have eq6141 : ∀ X2 X3 X4 : G, (M.op x y) = (M.op (M.op (M.op (M.op x (M.op (M.op x y) X2)) (M.op (M.op x y) X3)) (M.op (M.op x y) X4)) (M.op x y)) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq5971 x x X2 X3 X4
       have i₂ := eq14 x x x
       grind)
    | exact superpose eq14 eq5971
    | exact resolve eq5971 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5971
  have eq16650 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16658 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq16650
    | exact resolve eq16650 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16650
  have eq16669 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq16658
       have r₂ := eq27
       grind)
    | exact resolve eq16658 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16658
  have eq16671 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq16669
    | exact resolve eq16669 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16669
  have eq16681 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq16671 eq5261
    | exact resolve eq5261 eq16671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5261 eq16671
  have eq16738 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq28 eq16681
    | exact resolve eq16681 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq16681
  have eq16752 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq16738 X0
       have j1 := eq67 X0 x
       grind)
    | (have r₁ := eq16738 X0
       have r₂ := eq67 X0 x
       grind)
    | exact resolve eq16738 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq16738
  have eq16776 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq16752 y
       grind)
    | exact superpose eq16752 eq73
    | exact resolve eq73 eq16752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16791 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq512 x
       have i₂ := eq16752 x
       grind)
    | exact superpose eq16752 eq512
    | (have j0 := eq512 x
       grind)
    | exact resolve eq512 eq16752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512 eq16752
  have eq16814 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16791
  have eq16832 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16814
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16814
    | exact resolve eq16814 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16814
  have eq16846 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16776
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16776
    | exact resolve eq16776 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16776
  have eq16877 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16846
       have r₂ := eq51
       grind)
    | exact resolve eq16846 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq16846
  have eq16891 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16877 eq80
    | exact resolve eq80 eq16877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq16892 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16877 eq115
    | exact resolve eq115 eq16877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq16877
  have eq16905 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq16892
  have eq16914 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq16891
    | exact resolve eq16891 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16891
  have eq16919 : y = (k y x) := by
    first
    | (have r₁ := eq16914
       have r₂ := eq50
       grind)
    | exact resolve eq16914 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq16914
  have eq17089 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq16919
       grind)
    | exact superpose eq16919 eq73
    | exact resolve eq73 eq16919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq16919
  have eq17114 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq17089
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17089
    | exact resolve eq17089 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17089
  have eq18094 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16832 eq3673
    | exact resolve eq3673 eq16832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3673
  have eq18162 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq385 eq18094
    | exact resolve eq18094 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18094
  have eq18310 : x = (M.op (M.op x (M.op x y)) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq3672
       have i₂ := eq16905
       grind)
    | exact superpose eq16905 eq3672
    | exact resolve eq3672 eq16905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3672
  have eq18378 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq383 eq18310
    | exact resolve eq18310 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18310
  have eq18557 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18162 eq57
    | exact resolve eq57 eq18162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18162
  have eq19015 : y = (M.op (M.op x x) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq18378 eq56
    | exact resolve eq56 eq18378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq18378
  have eq29985 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16832 eq18557
    | exact resolve eq18557 eq16832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16832 eq18557
  have eq30023 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq29985
  have eq30038 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq30023
    | exact resolve eq30023 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30023
  have eq30316 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30038 eq27
    | exact resolve eq27 eq30038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30038
  have eq36741 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq19015
       have i₂ := eq16905
       grind)
    | exact superpose eq16905 eq19015
    | exact resolve eq19015 eq16905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16905 eq19015
  have eq36783 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq36741
  have eq36796 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36783
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq36783
    | exact resolve eq36783 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36783
  have eq36802 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36796 eq29
    | exact resolve eq29 eq36796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq36796
  have eq36968 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq36802
    | exact resolve eq36802 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36802
  have eq36969 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq36968
  have eq36980 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36969 eq20
    | exact resolve eq20 eq36969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36969
  have eq37158 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36980
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36980
    | exact resolve eq36980 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36980
  have eq37252 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37158 eq17114
    | exact resolve eq17114 eq37158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17114
  have eq37266 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37158 eq30316
    | (have r₁ := eq30316
       have r₂ := eq37158
       grind)
    | exact resolve eq30316 eq37158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30316
  have eq37269 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq37266
  have eq37270 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq37269
  have eq37353 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq37270 eq57
    | exact resolve eq57 eq37270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37361 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37270 eq385
    | exact resolve eq385 eq37270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37270
  have eq37397 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq37353 X0
       have i₂ := eq362 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq37353 x
       have i₂ := eq362 sF2 x
       grind)
    | exact superpose eq362 eq37353
    | exact resolve eq37353 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37353
  have eq37516 : (τ (σ (M.op x y))) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37252 eq148
    | exact resolve eq148 eq37252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq37252
  have eq37541 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq37516
    | exact resolve eq37516 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq37516
  have eq37544 : (M.op x y) = (k (M.op x y) x) := by
    first
    | (have r₁ := eq37541
       have r₂ := eq401
       grind)
    | exact resolve eq37541 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401 eq37541
  have eq37547 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq37544 eq128
    | exact resolve eq128 eq37544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37544
  have eq37579 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq37547
    | exact resolve eq37547 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37547
  have eq44287 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37361 eq37397
    | exact resolve eq37397 eq37361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37361 eq37397
  have eq44358 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq44287
  have eq44382 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq44358
    | exact resolve eq44358 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44358
  have eq44388 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq44382 eq27
    | exact resolve eq27 eq44382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44382
  have eq44443 : x = (M.op x y) := by
    first
    | (have r₁ := eq44388
       have r₂ := eq37158
       grind)
    | exact resolve eq44388 eq37158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37158 eq44388
  have eq44445 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq44443 eq20
    | exact resolve eq20 eq44443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44505 : x = (M.op x x) := by
    first
    | exact superpose eq44443 eq383
    | exact resolve eq383 eq44443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq44647 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq44445
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44445
    | exact resolve eq44445 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44445
  have eq44678 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq44647 eq26
    | exact resolve eq26 eq44647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq44706 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq44647 eq385
    | exact resolve eq385 eq44647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq45172 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k X0 x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq44647 eq4928
    | (have j0 := eq4928 x
       grind)
    | exact resolve eq4928 eq44647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4928
  have eq45173 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) ≠ (σ (k X0 x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq44647 eq45172
    | (have j0 := eq45172 X0
       grind)
    | exact resolve eq45172 eq44647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45172
  have eq45174 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k X0 x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq44647 eq45173
    | (have j0 := eq45173 X0
       grind)
    | exact resolve eq45173 eq44647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45173
  have eq45211 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq128 eq45174
    | (have j0 := eq45174 (M.op x y)
       grind)
    | exact resolve eq45174 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq45174
  have eq45212 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq45211
       have r₂ := eq37579
       grind)
    | exact resolve eq45211 eq37579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37579 eq45211
  have eq45238 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq45212
    | exact resolve eq45212 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq45212
  have eq45239 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq45238
  have eq46199 : ∀ X2 X3 X4 : G, x = (M.op (M.op (M.op (M.op x (M.op x X2)) (M.op x X3)) (M.op x X4)) x) := by
    intro X2 X3 X4
    first
    | exact superpose eq44443 eq6141
    | exact resolve eq6141 eq44443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6141
  have eq46200 : ∀ X2 X3 X4 : G, x = (M.op (M.op (M.op (M.op x X2) (M.op x X3)) (M.op x X4)) x) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq46199 X2 X3 X4
       have i₂ := eq362 x X2
       grind)
    | (have i₁ := eq46199 X2 X3 X4
       have i₂ := eq362 x (M.op x X2)
       grind)
    | exact superpose eq362 eq46199
    | exact resolve eq46199 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq46199
  have eq46242 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq46200 X0 X0 X0
       have i₂ := eq3637 (M.op x X0)
       grind)
    | exact superpose eq3637 eq46200
    | exact resolve eq46200 eq3637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3637 eq46200
  have eq46366 : (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq44706 eq4476
    | exact resolve eq4476 eq44706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4476
  have eq46371 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq45239 eq46366
    | exact resolve eq46366 eq45239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46366
  have eq46374 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq44706 eq46371
    | exact resolve eq46371 eq44706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44706 eq46371
  have eq47070 : (σ y) = (M.op (M.op (σ x) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq46374 eq57
    | exact resolve eq57 eq46374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq46374
  have eq47127 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq44647 eq47070
    | exact resolve eq47070 eq44647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47070
  have eq47137 : (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq45239 eq47127
    | exact resolve eq47127 eq45239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45239 eq47127
  have eq47140 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44678 eq47137
    | exact resolve eq47137 eq44678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44678 eq47137
  have eq47144 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq47140 eq27
    | exact resolve eq27 eq47140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq47140
  have eq48689 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq46242 X0
       grind)
    | exact superpose eq46242 eq14
    | exact resolve eq14 eq46242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46242
  have eq48751 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq48689 X0
       have i₂ := eq44505
       grind)
    | exact superpose eq44505 eq48689
    | exact resolve eq48689 eq44505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44505 eq48689
  have eq48801 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq48751 y
       grind)
    | exact superpose eq48751 eq18
    | (have j1 := eq48751 y
       grind)
    | exact resolve eq18 eq48751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq48751
  have eq48933 : x = y := by
    first
    | exact superpose eq44443 eq48801
    | exact resolve eq48801 eq44443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44443 eq48801
  have eq49991 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq48933
       grind)
    | exact superpose eq48933 eq24
    | exact resolve eq24 eq48933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq48933
  have eq50157 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq49991
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq49991
    | exact resolve eq49991 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq49991
  have eq50221 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq44647 eq50157
    | exact resolve eq50157 eq44647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44647 eq50157
  have eq50277 : False := by grind
  exact eq50277

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxx_pxy_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) X2) X1 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq88 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq20 X0 X1 X2 X3
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X4
       have i₂ := eq20 X0 X1 X2 X3
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq88 X0 x x X3 X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq88
    | exact resolve eq88 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq120 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
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
  have eq130 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq120 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq120
    | (have j0 := eq120 X0
       grind)
    | exact resolve eq120 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq120
  have eq131 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq130 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq130
    | (have j0 := eq130 X0
       grind)
    | exact resolve eq130 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq132 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq131 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq131 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq131 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq135 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq132 (σ X0)
       grind)
    | exact superpose eq132 eq15
    | exact resolve eq15 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq132 (τ X0)
       grind)
    | exact superpose eq132 eq35
    | exact resolve eq35 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq144 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq137 X0
       have i₂ := eq132 X0
       grind)
    | exact superpose eq132 eq137
    | exact resolve eq137 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq146 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq135 X0
       have i₂ := eq132 X0
       grind)
    | exact superpose eq132 eq135
    | exact resolve eq135 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq135
  have eq226 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
  clear eq79
  have eq387 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq95 (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3) X0
       have i₂ := eq20 X0 X1 X2 X3
       grind)
    | exact superpose eq20 eq95
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20 X0 X0 x X0
       have i₂ := eq95 X0 X0 x
       grind)
    | exact superpose eq95 eq20
    | exact resolve eq20 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq387 X0 X1 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq387
    | exact resolve eq387 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq424 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq95 X0 X0 X0
       have i₂ := eq402 X0
       grind)
    | exact superpose eq402 eq95
    | exact resolve eq95 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq537 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 (M.op X0 X0) (M.op X0 X0) x
       have i₂ := eq424 X0
       grind)
    | exact superpose eq424 eq95
    | exact resolve eq95 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq548 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq537 X0 X1
       have i₂ := eq21 X0 X0 X1
       grind)
    | exact superpose eq21 eq537
    | exact resolve eq537 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq537
  have eq874 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X1 X2)) (M.op X1 X3)) X1) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq93 X1 (M.op X0 X0) (M.op X0 X0) X2 X3
       have i₂ := eq548 X0 X1
       grind)
    | exact superpose eq548 eq93
    | exact resolve eq93 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq878 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X1 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X1 (M.op X0 X0) (M.op X0 X0) X2
       have i₂ := eq548 X0 X1
       grind)
    | exact superpose eq548 eq20
    | exact resolve eq20 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq879 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq548 X0 X1
       grind)
    | exact superpose eq548 eq9
    | exact resolve eq9 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq895 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq879 X0 X1
       have i₂ := eq424 X0
       grind)
    | exact superpose eq424 eq879
    | exact resolve eq879 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq896 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq878 X0 X1 X2
       have i₂ := eq424 X0
       grind)
    | exact superpose eq424 eq878
    | exact resolve eq878 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq899 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X2)) (M.op X1 X3)) X1) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq874 X0 X1 X2 X3
       have i₂ := eq424 X0
       grind)
    | exact superpose eq424 eq874
    | exact resolve eq874 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424 eq874
  have eq901 : ∀ X1 X2 : G, (M.op (M.op X1 X2) X1) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq896 x X1 X2
       have i₂ := eq895 x (M.op X1 X2)
       grind)
    | exact superpose eq895 eq896
    | exact resolve eq896 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq903 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X1 X3)) X1) = X1 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq899 x X1 X2 X3
       have i₂ := eq895 x (M.op X1 X2)
       grind)
    | exact superpose eq895 eq899
    | exact resolve eq899 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq906 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq895 (σ X0) X1
       have i₂ := eq146 X0
       grind)
    | exact superpose eq146 eq895
    | exact resolve eq895 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq908 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq895 (τ X0) X1
       have i₂ := eq144 X0
       grind)
    | exact superpose eq144 eq895
    | exact resolve eq895 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq909 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq548 X1 X0
       have i₂ := eq895 X1 X0
       grind)
    | exact superpose eq895 eq548
    | exact resolve eq548 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq1029 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X0) X2)) = (M.op X0 (M.op X1 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq901 (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq901
    | exact resolve eq901 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1195 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (M.op X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq901 (τ (M.op X1 X1)) X0
       have i₂ := eq908 X1 X0
       grind)
    | exact superpose eq908 eq901
    | exact resolve eq901 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq1691 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq226
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq226
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq226
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq226
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq226 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq1692 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1691
  have eq1732 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X2) X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq903 (M.op X0 X1) X2 X0
       have i₂ := eq901 X0 X1
       grind)
    | exact superpose eq901 eq903
    | exact resolve eq903 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq26259 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1692
       grind)
    | exact superpose eq1692 eq16
    | exact resolve eq16 eq1692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1692
  have eq26260 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq26259
       have r₂ := eq146 x
       grind)
    | exact resolve eq26259 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26259
  have eq30477 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 (M.op (M.op X0 X0) X1)) (M.op X0 X2)) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X1) X0 (M.op X0 X2)
       have i₂ := eq419 X0 X0 X1 X2
       grind)
    | exact superpose eq419 eq9
    | exact resolve eq9 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq30599 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30477 X0 X1 X2
       have i₂ := eq895 X0 X1
       grind)
    | exact superpose eq895 eq30477
    | exact resolve eq30477 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895 eq30477
  have eq30827 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X0) X3) (M.op X0 X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30599 (M.op (M.op (M.op X0 X1) X2) X0) X3 (M.op X0 X1)
       have i₂ := eq1732 X0 X1 X2
       grind)
    | exact superpose eq1732 eq30599
    | exact resolve eq30599 eq1732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1732
  have eq30828 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30599 (M.op X0 X1) X2 X0
       have i₂ := eq901 X0 X1
       grind)
    | exact superpose eq901 eq30599
    | exact resolve eq30599 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30909 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X1 X0) X0) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X2) (M.op X1 X0) X0
       have i₂ := eq30599 X1 X0 X2
       grind)
    | exact superpose eq30599 eq9
    | exact resolve eq9 eq30599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30599
  have eq31088 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2))) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30828 (M.op X1 (M.op (M.op X1 X0) X2)) X0 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq30828
    | exact resolve eq30828 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31213 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X0) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op (M.op X1 X2) X0) X0
       have i₂ := eq30828 X1 X2 X0
       grind)
    | exact superpose eq30828 eq9
    | exact resolve eq9 eq30828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30828
  have eq31948 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op (M.op X0 X2) X2) X3) X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30909 X0 (M.op (M.op X1 X0) X0) (M.op X1 X2)
       have i₂ := eq30909 X0 X1 X2
       grind)
    | exact superpose eq30909 eq30909
    | exact resolve eq30909 eq30909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95290 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op (M.op X0 X1) X1) X2)) X3)) X2) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq31088 (M.op (M.op (M.op X0 X1) X1) X2) X0 X3 X2
       have i₂ := eq31948 X0 (M.op (M.op X0 (M.op (M.op (M.op X0 X1) X1) X2)) X3) X1 X2
       grind)
    | exact superpose eq31948 eq31088
    | exact resolve eq31088 eq31948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31088 eq31948
  have eq96799 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X3))) X2) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X1 (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X3))
       have i₂ := eq1029 (M.op X1 X2) X0 X3
       grind)
    | exact superpose eq1029 eq9
    | exact resolve eq9 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq97463 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op (M.op X0 X2) (M.op X1 X3)) X0)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq96799 (M.op (M.op X0 X2) (M.op X1 X3)) X1 X3 X0
       have i₂ := eq31213 (M.op X1 X3) X0 X2
       grind)
    | exact superpose eq31213 eq96799
    | exact resolve eq96799 eq31213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31213
  have eq111731 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op (M.op X0 X1) X2) X0)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq97463 (M.op (M.op (M.op X0 X1) X2) X0) X0 (M.op (M.op (M.op X0 X1) X2) X0) X1
       have i₂ := eq30827 X0 X1 X2 (M.op (M.op (M.op X0 X1) X2) X0)
       grind)
    | exact superpose eq30827 eq97463
    | exact resolve eq97463 eq30827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30827 eq97463
  have eq113009 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 (M.op (M.op (M.op X1 X0) X2) X1)) X3) X3) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30909 X0 (M.op X0 (M.op (M.op (M.op X0 X1) X2) X0)) X1
       have i₂ := eq111731 X0 X1 X2
       grind)
    | exact superpose eq111731 eq30909
    | exact resolve eq30909 eq111731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30909 eq111731
  have eq142039 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op (M.op X1 X2) X2) X0)) (M.op X1 X0)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq96799 X1 (M.op X1 (M.op (M.op (M.op X1 X2) X2) X0)) X3 X0
       have i₂ := eq95290 X1 X2 X0 X3
       grind)
    | exact superpose eq95290 eq96799
    | exact resolve eq96799 eq95290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95290 eq96799
  have eq487947 : y = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq26260
       grind)
    | exact superpose eq26260 eq10
    | exact resolve eq10 eq26260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26260
  have eq488133 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq487947
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq487947
    | exact resolve eq487947 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487947
  have eq488140 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq488133
       grind)
    | exact superpose eq488133 eq16
    | exact resolve eq16 eq488133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488133
  have eq488141 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq488140
       have r₂ := eq146 x
       grind)
    | exact resolve eq488140 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq488140
  have eq488991 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq901 x y
       have i₂ := eq488141
       grind)
    | exact superpose eq488141 eq901
    | exact resolve eq901 eq488141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488141
  have eq489858 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) X0) X0) (σ y))) (σ x)) X1) = X1 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq142039 (σ y) (σ x) X0 X1
       have i₂ := eq488991
       grind)
    | exact superpose eq488991 eq142039
    | exact resolve eq142039 eq488991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142039 eq488991
  have eq490066 : ∀ X1 : G, x = (M.op x x) ∨ (M.op (σ x) X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq489858 x X1
       have i₂ := eq901 (σ x) (M.op (M.op (M.op (σ x) x) x) (σ y))
       grind)
    | exact superpose eq901 eq489858
    | exact resolve eq489858 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901 eq489858
  have eq491124 : ∀ X0 X1 : G, (M.op (σ x) X1) = X1 ∨ x = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq909 X0 x
       have i₂ := eq490066 X1
       grind)
    | exact superpose eq490066 eq909
    | (have j1 := eq490066 X1
       grind)
    | exact resolve eq909 eq490066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909 eq490066
  have eq493832 : ∀ X0 X1 : G, (τ (σ x)) = (M.op X0 (τ (σ x))) ∨ x = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq1195 X0 (σ x)
       have i₂ := eq491124 X0 (σ x)
       grind)
    | exact superpose eq491124 eq1195
    | (have j1 := eq491124 X1 X1
       grind)
    | exact resolve eq1195 eq491124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195 eq491124
  have eq494876 : ∀ X0 X1 : G, x = (M.op X0 x) ∨ x = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq493832 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq493832
    | (have j0 := eq493832 X0 X0
       grind)
    | exact resolve eq493832 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493832
  have eq499001 : ∀ X0 : G, x ≠ x ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq494876 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494876
  have eq499002 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq499001 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499001
  have eq499045 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq906 x X0
       have i₂ := eq499002 x
       grind)
    | exact superpose eq499002 eq906
    | exact resolve eq906 eq499002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq499889 : ∀ X1 : G, (M.op x X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq113009 X1 x x x
       have i₂ := eq499002 (M.op (M.op x (M.op (M.op (M.op x X1) x) x)) x)
       grind)
    | exact superpose eq499002 eq113009
    | exact resolve eq113009 eq499002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113009 eq499002
  have eq504366 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq499045 (σ y)
       grind)
    | exact superpose eq499045 eq16
    | exact resolve eq16 eq499045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499045
  have eq505784 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq504366
       have i₂ := eq499889 y
       grind)
    | (have i₁ := eq504366
       have i₂ := eq499889 (M.op x y)
       grind)
    | exact superpose eq499889 eq504366
    | exact resolve eq504366 eq499889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499889 eq504366
  have eq505785 : False := by grind
  exact eq505785

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_x_pxx_x_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  clear eq22
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
  clear eq40
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
  have eq174 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq175 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, y = (M.op (M.op (M.op x (M.op (M.op x y) X0)) (M.op y X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ y) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq550 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op x (M.op (M.op x y) X0)) y) (M.op y X1)) := by
    intro X0 X1
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq552 : ∀ X1 : G, (M.op y X1) = (M.op y (M.op y X1)) := by
    intro X1
    first
    | exact superpose eq174 eq550
    | exact resolve eq550 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq550
  have eq557 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq183 eq16
    | exact resolve eq16 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq559 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (σ y) (M.op (σ y) X1)) := by
    intro X1
    first
    | exact superpose eq175 eq557
    | exact resolve eq557 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq557
  have eq823 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X1 (M.op (M.op X1 X0) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq11 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq832 : (M.op x y) = (k y x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq842 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq853 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq854 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq853 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq871 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X1 (M.op (M.op X1 X0) X2))) = X0 ∨ (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq823 X0 X1 X2
       have j1 := eq12 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       grind)
    | (have r₁ := eq823 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq823 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq885 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq854 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq854
    | (have j0 := eq854 (σ X0)
       grind)
    | exact resolve eq854 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1855 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq176 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1891 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq1855 X0 x x X3 X4
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1855
    | exact resolve eq1855 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1855
  have eq5223 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq832
       grind)
    | exact superpose eq832 eq39
    | exact resolve eq39 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq832
  have eq5224 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5223
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5223
    | exact resolve eq5223 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5223
  have eq5227 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq5224
    | exact resolve eq5224 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5224
  have eq15043 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq176 X0 X0 x X0
       have i₂ := eq1891 X0 X0 x
       grind)
    | exact superpose eq1891 eq176
    | exact resolve eq176 eq1891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq15083 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1891 X0 X0 X0
       have i₂ := eq15043 X0
       grind)
    | exact superpose eq15043 eq1891
    | exact resolve eq1891 eq15043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15299 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq15083 X0
       grind)
    | exact superpose eq15083 eq178
    | exact resolve eq178 eq15083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15310 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq178 (M.op X0 X0)
       have i₂ := eq15083 X0
       grind)
    | exact superpose eq15083 eq178
    | exact resolve eq178 eq15083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15330 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15310 X0
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq15310
    | exact resolve eq15310 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq15310
  have eq15339 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15330 X0
       have i₂ := eq15299 X0
       grind)
    | exact superpose eq15299 eq15330
    | exact resolve eq15330 eq15299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15330
  have eq15347 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 ∨ (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15299 (M.op X1 (M.op (M.op X1 X0) X2))
       have i₂ := eq871 X0 X1 X2
       grind)
    | exact superpose eq871 eq15299
    | (have j1 := eq871 X0 X1 X2
       grind)
    | exact resolve eq15299 eq871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq15383 : (τ (M.op (σ y) (σ y))) = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | (have i₁ := eq152 (M.op sF3 sF3)
       have i₂ := eq15299 sF3
       grind)
    | exact superpose eq15299 eq152
    | exact resolve eq152 eq15299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq15299
  have eq15384 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq15347 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15347
  have eq15694 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq15384 X0 X0 X0
       have i₂ := eq15043 X0
       grind)
    | exact superpose eq15043 eq15384
    | exact resolve eq15384 eq15043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15043
  have eq15908 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq107 (M.op sF3 sF3)
       have i₂ := eq15694 sF3
       grind)
    | exact superpose eq15694 eq107
    | exact resolve eq107 eq15694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq15694
  have eq15910 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq31 eq15908
    | exact resolve eq15908 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15908
  have eq16023 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq5227 eq842
    | exact resolve eq842 eq5227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842 eq5227
  have eq16031 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq16023
       have r₂ := eq27
       grind)
    | exact resolve eq16023 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16023
  have eq16051 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16031 eq15383
    | exact resolve eq15383 eq16031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15383 eq16031
  have eq16091 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq16051
    | exact resolve eq16051 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16051
  have eq16094 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq854 y
       grind)
    | (have r₁ := eq16091
       have r₂ := eq854 y
       grind)
    | exact resolve eq16091 eq854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16091
  have eq16108 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16094 eq15083
    | exact resolve eq15083 eq16094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15083 eq16094
  have eq16573 : y = (k y (τ (σ y))) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16108 eq15910
    | exact resolve eq15910 eq16108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15910 eq16108
  have eq16615 : y = (k y y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq16573
    | exact resolve eq16573 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq16573
  have eq16626 : y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq854 y
       grind)
    | (have r₁ := eq16615
       have r₂ := eq854 y
       grind)
    | exact resolve eq16615 eq854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16615
  have eq16652 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1891 y y x
       have i₂ := eq16626
       grind)
    | exact superpose eq16626 eq1891
    | exact resolve eq1891 eq16626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16658 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq16652 X0
       have i₂ := eq552 X0
       grind)
    | (have i₁ := eq16652 X0
       have i₂ := eq552 (M.op y X0)
       grind)
    | exact superpose eq552 eq16652
    | exact resolve eq16652 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16652
  have eq16784 : ∀ X0 : G, (k X0 (M.op y y)) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq15384 X0 y y
       have i₂ := eq16658 X0
       grind)
    | exact superpose eq16658 eq15384
    | exact resolve eq15384 eq16658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15384 eq16658
  have eq16804 : ∀ X0 : G, y = (M.op x x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq16626 eq16784
    | exact resolve eq16784 eq16626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16626 eq16784
  have eq16832 : ∀ X0 : G, y = (k y y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq15339 x
       have i₂ := eq16804 X0
       grind)
    | exact superpose eq16804 eq15339
    | (have j1 := eq16804 y
       grind)
    | exact resolve eq15339 eq16804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15339 eq16804
  have eq19031 : y ≠ y ∨ y = (k y y) := by
    first
    | (have j0 := eq16832 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16832
  have eq19032 : y = (k y y) := by grind
  clear eq19031
  have eq19053 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq885 y
       have i₂ := eq19032
       grind)
    | exact superpose eq19032 eq885
    | (have j0 := eq885 y
       grind)
    | exact resolve eq885 eq19032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq19056 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq854 y
       have i₂ := eq19032
       grind)
    | exact superpose eq19032 eq854
    | (have j0 := eq854 y
       grind)
    | (have r₁ := eq854 y
       have r₂ := eq19032
       grind)
    | exact resolve eq854 eq19032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854 eq19032
  have eq19059 : y = (M.op y y) := by grind
  clear eq19056
  have eq19061 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq19053
  have eq19063 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq19061
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19061
    | exact resolve eq19061 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19061
  have eq19096 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq1891 y y x
       have i₂ := eq19059
       grind)
    | exact superpose eq19059 eq1891
    | exact resolve eq1891 eq19059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19102 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq19096 X0
       have i₂ := eq552 X0
       grind)
    | (have i₁ := eq19096 X0
       have i₂ := eq552 (M.op y X0)
       grind)
    | exact superpose eq552 eq19096
    | exact resolve eq19096 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq19096
  have eq19140 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq19063 eq1891
    | exact resolve eq1891 eq19063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1891
  have eq19146 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq559 eq19140
    | exact resolve eq19140 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq19140
  have eq19217 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq19102 X0
       grind)
    | exact superpose eq19102 eq16
    | exact resolve eq16 eq19102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19243 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19217 X0
       have i₂ := eq19059
       grind)
    | exact superpose eq19059 eq19217
    | exact resolve eq19217 eq19059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19059 eq19217
  have eq19426 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq19102 X0
       have i₂ := eq19243 X0
       grind)
    | exact superpose eq19243 eq19102
    | exact resolve eq19102 eq19243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19102 eq19243
  have eq19860 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq19426 x
       grind)
    | exact superpose eq19426 eq18
    | (have j1 := eq19426 x
       grind)
    | exact resolve eq18 eq19426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19426
  have eq19918 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq19860
       grind)
    | exact superpose eq19860 eq24
    | exact resolve eq24 eq19860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq19860
  have eq20020 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19918 eq20
    | exact resolve eq20 eq19918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq19918
  have eq22792 : ∀ X0 : G, (M.op (M.op (σ y) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq19146 eq16
    | exact resolve eq16 eq19146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22823 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq19063 eq22792
    | exact resolve eq22792 eq19063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19063 eq22792
  have eq22833 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq22823 eq19146
    | exact resolve eq19146 eq22823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19146 eq22823
  have eq22964 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22833 eq26
    | (have j1 := eq22833 (σ x)
       grind)
    | exact resolve eq26 eq22833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq22833
  have eq23002 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq22964 eq27
    | exact resolve eq27 eq22964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq22964
  have eq23024 : False := by grind
  exact eq23024
