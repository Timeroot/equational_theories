import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2314`: `x = (y ◇ (x ◇ (z ◇ y))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pyx_pxy_pyx_Equation2314 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2314 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2314.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq73 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq73 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq73 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq73 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq73 X0 X1
       grind)
    | exact resolve eq13 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq251 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq232 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq252 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq251 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq256 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq252 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq252 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq252 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq265 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq256 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq256
    | (have j0 := eq256 X0 X1
       grind)
    | exact resolve eq256 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq266 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq265 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq271 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq266 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq266
    | exact resolve eq266 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq266 x y
       grind)
    | exact superpose eq266 eq16
    | exact resolve eq16 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq328 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq271 X0 (τ X1)
       grind)
    | exact superpose eq271 eq17
    | exact resolve eq17 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq271
  have eq342 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq328 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq328
    | exact resolve eq328 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq348 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq342 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq342
    | exact resolve eq342 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq366 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq282
       have i₂ := eq348 x y
       grind)
    | exact superpose eq348 eq282
    | exact resolve eq282 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282 eq348
  have eq367 : False := by grind
  exact eq367

/-- `Equation2368`: `x = (y ◇ (z ◇ (x ◇ y))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyx_x_pyx_x_pyx_Equation2368 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2368 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2368.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq72 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ y = (k y x) := by
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
  have eq73 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq69
       have i₂ := eq91 y x
       grind)
    | exact superpose eq91 eq69
    | (have j1 := eq91 y x
       grind)
    | exact resolve eq69 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq117 eq91
    | (have j0 := eq91 (σ y) (σ x)
       grind)
    | exact resolve eq91 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq120
    | exact resolve eq120 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq124 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq121
       have r₂ := eq27
       grind)
    | exact resolve eq121 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq126 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq124
    | exact resolve eq124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq126 eq27
    | exact resolve eq27 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq126 eq73
    | (have r₁ := eq73
       have r₂ := eq126
       grind)
    | exact resolve eq73 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq126
  have eq362 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq361
  have eq365 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq362 eq117
    | exact resolve eq117 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq369 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq365
  have eq374 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq369
       have r₂ := eq128
       grind)
    | exact resolve eq369 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq369
  have eq382 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq374 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) x
       have r₂ := eq374
       grind)
    | exact resolve eq13 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq385 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq382 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq444 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq385 eq117
    | exact resolve eq117 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq385
  have eq447 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq444
  have eq452 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq447
    | exact resolve eq447 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq454 : y = (M.op x y) := by
    first
    | (have r₁ := eq452
       have r₂ := eq27
       grind)
    | exact resolve eq452 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq497 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq454 eq20
    | exact resolve eq20 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq501 : y ≠ y ∨ y = (M.op y y) ∨ y = (k y x) := by
    first
    | exact superpose eq454 eq72
    | (have r₁ := eq72
       have r₂ := eq454
       grind)
    | exact resolve eq72 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq454
  have eq506 : y = (k y x) ∨ y = (M.op y y) := by grind
  clear eq501
  have eq512 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq497
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq497
    | exact resolve eq497 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq513 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq512 eq26
    | exact resolve eq26 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq723 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq69
       have i₂ := eq506
       grind)
    | exact superpose eq506 eq69
    | exact resolve eq69 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq730 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq512 eq723
    | exact resolve eq723 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq732 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq730
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq730
    | exact resolve eq730 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq730
  have eq733 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq512 eq732
    | exact resolve eq732 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq760 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq733 eq91
    | (have j0 := eq91 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq91 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq761 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by grind
  clear eq760
  have eq763 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq513 eq761
    | exact resolve eq761 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq766 : y = (M.op y y) := by
    first
    | (have r₁ := eq763
       have r₂ := eq27
       grind)
    | exact resolve eq763 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq775 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq766
       grind)
    | exact superpose eq766 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq766
       grind)
    | exact resolve eq13 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq780 : ∀ X0 : G, (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq775 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq825 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq780 x
       grind)
    | exact superpose eq780 eq69
    | exact resolve eq69 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq780
  have eq830 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq512 eq825
    | exact resolve eq825 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512 eq825
  have eq834 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq830
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq830
    | exact resolve eq830 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq830
  have eq838 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq834
    | exact resolve eq834 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq834
  have eq844 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq838 eq91
    | (have j0 := eq91 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq91 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq838
  have eq845 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq844
  have eq847 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq513 eq845
    | exact resolve eq845 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513 eq845
  have eq850 : False := by grind
  exact eq850

/-- `Equation2372`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxx_pxy_pyx_Equation2372 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2372 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2372.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq70 (σ X0)
       grind)
    | exact superpose eq70 eq15
    | exact resolve eq15 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq73
    | exact resolve eq73 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq73
  have eq522 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq529 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq522 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq625 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq529 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq629 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq625 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq625 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq625 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq625 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq625 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq681 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq629 X1 (τ X0)
       grind)
    | exact superpose eq629 eq19
    | (have j1 := eq629 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq684 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq629 (σ X1) (σ X0)
       grind)
    | exact superpose eq629 eq15
    | (have j1 := eq629 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq753 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq681 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq681
    | exact resolve eq681 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq792 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq753 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq753
    | (have j0 := eq753 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq753 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq950 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq684 x y
       grind)
    | exact superpose eq684 eq16
    | (have j1 := eq684 x y
       grind)
    | exact resolve eq16 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq975 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq950
       have i₂ := eq792 x y
       grind)
    | exact superpose eq792 eq950
    | (have j1 := eq792 (σ x) (σ y)
       grind)
    | (have r₁ := eq950
       have r₂ := eq792 x y
       grind)
    | (have r₁ := eq950
       have r₂ := eq792 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq950
       have r₂ := eq792 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq950 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792 eq950
  have eq976 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq975
  have eq980 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq976
       grind)
    | exact superpose eq976 eq10
    | exact resolve eq10 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
  have eq1021 : x = y ∨ x = y := by
    first
    | (have i₁ := eq980
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq980
    | exact resolve eq980 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980
  have eq1022 : x = y := by grind
  clear eq1021
  have eq1024 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1022
       grind)
    | exact superpose eq1022 eq16
    | exact resolve eq16 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1025 : False := by grind
  exact eq1025

/-- `Equation2406`: `x = (y ◇ (z ◇ (z ◇ z))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pxx_pyy_pyx_Equation2406 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2406 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2406.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X2 X2))) X0) = X0 := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq176 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X0)) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq16 X3 (M.op x (M.op x (M.op x x))) X0
       have i₂ := eq16 (M.op X0 (M.op X0 X0)) x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1098 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1099 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1126 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) := by
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
  have eq1127 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1128 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1132 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1128 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq1128 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq1128 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128
  have eq1139 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq1132 X0
       grind)
    | exact superpose eq1132 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1141 : ∀ X0 X1 : G, (M.op (M.op X0 (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 X1
       have i₂ := eq1132 X0
       grind)
    | exact superpose eq1132 eq176
    | exact resolve eq176 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1161 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1139 X0 X1
       have i₂ := eq1132 X1
       grind)
    | exact superpose eq1132 eq1139
    | (have j0 := eq1139 X0 X1
       grind)
    | exact resolve eq1139 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139
  have eq1165 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ (k X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1141 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1141
    | exact resolve eq1141 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2980 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1098
       grind)
    | exact superpose eq1098 eq39
    | exact resolve eq39 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098
  have eq2981 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2980
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2980
    | exact resolve eq2980 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2980
  have eq2983 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq2981
    | exact resolve eq2981 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2981
  have eq2985 : (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2983
       have i₂ := eq1132 x
       grind)
    | exact superpose eq1132 eq2983
    | exact resolve eq2983 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2983
  have eq2987 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq2985
       have i₂ := eq1132 x
       grind)
    | exact superpose eq1132 eq2985
    | exact resolve eq2985 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2985
  have eq6742 : (M.op x y) ≠ (k x x) ∨ x = (k x x) ∨ (k x x) = (k y x) := by
    first
    | (have i₁ := eq1126
       have i₂ := eq1132 x
       grind)
    | exact superpose eq1132 eq1126
    | exact resolve eq1126 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq6743 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1127
       have i₂ := eq1132 sF2
       grind)
    | exact superpose eq1132 eq1127
    | exact resolve eq1127 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq40774 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    first
    | exact superpose eq2987 eq1099
    | exact resolve eq1099 eq2987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40781 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    first
    | (have r₁ := eq40774
       have r₂ := eq27
       grind)
    | exact resolve eq40774 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40774
  have eq40787 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq40781
       have i₂ := eq1132 sF2
       grind)
    | exact superpose eq1132 eq40781
    | exact resolve eq40781 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40781
  have eq40789 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq40787
       have i₂ := eq1132 sF2
       grind)
    | exact superpose eq1132 eq40787
    | exact resolve eq40787 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40787
  have eq41328 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by grind
  have eq68507 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    first
    | exact superpose eq40789 eq6743
    | (have r₁ := eq6743
       have r₂ := eq40789
       grind)
    | exact resolve eq6743 eq40789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6743 eq40789
  have eq68508 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by grind
  clear eq68507
  have eq68509 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    first
    | (have r₁ := eq68508
       have r₂ := eq41328
       grind)
    | exact resolve eq68508 eq41328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41328 eq68508
  have eq68510 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    first
    | exact superpose eq2987 eq68509
    | exact resolve eq68509 eq2987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2987 eq68509
  have eq68511 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    first
    | (have r₁ := eq68510
       have r₂ := eq27
       grind)
    | exact resolve eq68510 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68510
  have eq68517 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    first
    | exact superpose eq68511 eq141
    | exact resolve eq141 eq68511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq68511
  have eq68673 : x = (k x x) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq68517
    | exact resolve eq68517 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68517
  have eq68674 : (M.op x y) = (k x x) ∨ x = (k x x) := by grind
  clear eq68673
  have eq68758 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq6742
       have i₂ := eq68674
       grind)
    | exact superpose eq68674 eq6742
    | (have r₁ := eq6742
       have r₂ := eq68674
       grind)
    | exact resolve eq6742 eq68674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6742
  have eq68762 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq68674
       grind)
    | exact superpose eq68674 eq39
    | exact resolve eq39 eq68674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68840 : x ≠ (M.op x y) ∨ x = (k x x) := by grind
  clear eq68674
  have eq68841 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (k x x) := by grind
  clear eq68758
  have eq68858 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq68762
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq68762
    | exact resolve eq68762 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68762
  have eq68862 : (M.op x y) = (k y x) ∨ x = (k x x) := by
    first
    | (have r₁ := eq68841
       have r₂ := eq68840
       grind)
    | exact resolve eq68841 eq68840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68841
  have eq68876 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq20 eq68858
    | exact resolve eq68858 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68858
  have eq68882 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq68862
       grind)
    | exact superpose eq68862 eq39
    | exact resolve eq39 eq68862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68862
  have eq68883 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq68882
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq68882
    | exact resolve eq68882 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68882
  have eq68887 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq20 eq68883
    | exact resolve eq68883 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68883
  have eq69020 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq68887 eq1099
    | exact resolve eq1099 eq68887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099 eq68887
  have eq69027 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have r₁ := eq69020
       have r₂ := eq27
       grind)
    | exact resolve eq69020 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69020
  have eq69033 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq69027
       have i₂ := eq1132 sF2
       grind)
    | exact superpose eq1132 eq69027
    | exact resolve eq69027 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69027
  have eq69035 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq69033
       have i₂ := eq1132 sF2
       grind)
    | exact superpose eq1132 eq69033
    | exact resolve eq69033 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69033
  have eq69037 : (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq68876 eq69035
    | exact resolve eq69035 eq68876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69035
  have eq69039 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq68876 eq69037
    | exact resolve eq69037 eq68876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68876 eq69037
  have eq69041 : x = (k x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq69039
       have r₂ := eq27
       grind)
    | exact resolve eq69039 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69039
  have eq69048 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq69041
       grind)
    | exact superpose eq69041 eq39
    | exact resolve eq39 eq69041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69050 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1141 x X0
       have i₂ := eq69041
       grind)
    | exact superpose eq69041 eq1141
    | exact resolve eq1141 eq69041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69057 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1165 x X0
       have i₂ := eq69041
       grind)
    | exact superpose eq69041 eq1165
    | exact resolve eq1165 eq69041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69195 : ∀ X0 : G, (M.op (k (σ x) (σ x)) X0) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq69057 X0
       have i₂ := eq1132 (σ x)
       grind)
    | exact superpose eq1132 eq69057
    | exact resolve eq69057 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69057
  have eq69201 : ∀ X0 : G, (M.op (k x x) X0) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq69050 X0
       have i₂ := eq1132 x
       grind)
    | exact superpose eq1132 eq69050
    | exact resolve eq69050 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69050
  have eq69203 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq69048
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq69048
    | exact resolve eq69048 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69048
  have eq69275 : ∀ X0 : G, (M.op (σ (k x x)) X0) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq69195 X0
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq69195
    | exact resolve eq69195 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69195
  have eq69281 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq69041 eq69201
    | exact resolve eq69201 eq69041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69041 eq69201
  have eq69329 : ∀ X0 : G, (M.op (k (σ x) (σ x)) X0) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq69275 X0
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq69275
    | exact resolve eq69275 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq69275
  have eq69365 : ∀ X0 : G, (M.op (k (σ x) (σ x)) X0) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq69329 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq69329
    | (have j0 := eq69329 X0
       grind)
    | exact resolve eq69329 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69329
  have eq69378 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq69203 eq69365
    | exact resolve eq69365 eq69203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69203 eq69365
  have eq69725 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq69281 y
       grind)
    | exact superpose eq69281 eq18
    | (have j1 := eq69281 y
       grind)
    | exact resolve eq18 eq69281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69281
  have eq70149 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq69725 eq28
    | exact resolve eq28 eq69725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq69725
  have eq70250 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq70149
    | exact resolve eq70149 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70149
  have eq70274 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq70250
       grind)
    | exact superpose eq70250 eq24
    | exact resolve eq24 eq70250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70321 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq70274
    | exact resolve eq70274 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70274
  have eq70450 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq69378 eq26
    | (have j1 := eq69378 (σ y)
       grind)
    | exact resolve eq26 eq69378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69378
  have eq70909 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq70450 eq27
    | exact resolve eq27 eq70450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70450
  have eq70980 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq70321 eq70909
    | (have r₁ := eq70909
       have r₂ := eq70321
       grind)
    | exact resolve eq70909 eq70321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70321 eq70909
  have eq70981 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq70980
  have eq70983 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq70981 eq31
    | exact resolve eq31 eq70981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq70981
  have eq71089 : x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq70983
    | exact resolve eq70983 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq70983
  have eq71139 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq70250 eq71089
    | exact resolve eq71089 eq70250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70250 eq71089
  have eq71140 : x = (M.op x y) := by grind
  clear eq71139
  have eq71157 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq71140
       grind)
    | exact superpose eq71140 eq18
    | exact resolve eq18 eq71140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq71158 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq71140
       grind)
    | exact superpose eq71140 eq22
    | exact resolve eq22 eq71140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq71219 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq68840
       have i₂ := eq71140
       grind)
    | exact superpose eq71140 eq68840
    | (have r₁ := eq68840
       have r₂ := eq71140
       grind)
    | exact resolve eq68840 eq71140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68840 eq71140
  have eq71223 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq71219
  have eq71284 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq71158 eq20
    | exact resolve eq20 eq71158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71974 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq71223 eq37
    | exact resolve eq37 eq71223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq71977 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq71223 eq1141
    | exact resolve eq1141 eq71223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq71983 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (k X0 X0) := by
    intro X0
    first
    | exact superpose eq71223 eq1161
    | (have j0 := eq1161 (M.op x y) X0
       grind)
    | (have r₁ := eq1161 (M.op x y) x
       have r₂ := eq71223
       grind)
    | exact resolve eq1161 eq71223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161
  have eq71984 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq71223 eq1165
    | exact resolve eq1165 eq71223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165
  have eq72053 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq71983 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71983
  have eq72122 : ∀ X0 : G, (M.op (k (σ (M.op x y)) (σ (M.op x y))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq71984 X0
       have i₂ := eq1132 (σ sF0)
       grind)
    | exact superpose eq1132 eq71984
    | exact resolve eq71984 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71984
  have eq72128 : ∀ X0 : G, (M.op (k (M.op x y) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq71977 X0
       have i₂ := eq1132 sF0
       grind)
    | exact superpose eq1132 eq71977
    | exact resolve eq71977 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132 eq71977
  have eq72131 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq71974
    | exact resolve eq71974 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71974
  have eq72202 : ∀ X0 : G, (M.op (σ (k (M.op x y) (M.op x y))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq72122 X0
       have i₂ := eq10 sF0 sF0
       grind)
    | exact superpose eq10 eq72122
    | exact resolve eq72122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72122
  have eq72208 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq71223 eq72128
    | exact resolve eq72128 eq71223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71223 eq72128
  have eq72211 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq72131
       have i₂ := eq72053 sF1
       grind)
    | exact superpose eq72053 eq72131
    | exact resolve eq72131 eq72053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72131
  have eq72259 : ∀ X0 : G, (M.op (k (σ (M.op x y)) (σ (M.op x y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq41 eq72202
    | exact resolve eq72202 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq72202
  have eq72262 : (σ x) = (k (σ x) (M.op x y)) := by
    first
    | exact superpose eq71284 eq72211
    | exact resolve eq72211 eq71284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72211
  have eq72298 : ∀ X0 : G, (M.op (k (σ (M.op x y)) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq71284 eq72259
    | exact resolve eq72259 eq71284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72259
  have eq72325 : ∀ X0 : G, (M.op (k (σ (M.op x y)) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq72298
    | (have j0 := eq72298 X0
       grind)
    | exact resolve eq72298 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq72298
  have eq72349 : ∀ X0 : G, (M.op (k (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq71284 eq72325
    | exact resolve eq72325 eq71284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72325
  have eq72369 : ∀ X0 : G, (M.op (k (σ x) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq72349 X0
       have i₂ := eq72053 sF2
       grind)
    | exact superpose eq72053 eq72349
    | exact resolve eq72349 eq72053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72053 eq72349
  have eq72381 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq72262 eq72369
    | exact resolve eq72369 eq72262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72262 eq72369
  have eq72390 : y = (M.op x y) := by
    first
    | exact superpose eq72208 eq71157
    | exact resolve eq71157 eq72208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71157 eq72208
  have eq72871 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq72390
       grind)
    | exact superpose eq72390 eq24
    | exact resolve eq24 eq72390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq72390
  have eq72918 : (σ x) = (σ y) := by
    first
    | exact superpose eq71158 eq72871
    | exact resolve eq72871 eq71158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71158 eq72871
  have eq72971 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq72918 eq26
    | exact resolve eq26 eq72918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq72918
  have eq73077 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72381 eq72971
    | exact resolve eq72971 eq72381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72381 eq72971
  have eq73196 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq73077 eq27
    | exact resolve eq27 eq73077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq73077
  have eq73269 : False := by grind
  exact eq73269

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_pyy_pyx_Equation2755 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2755 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X2 X2) (M.op X3 X0))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X1 (M.op (M.op X2 X2) (M.op X3 X0))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq18
  have eq31 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq27 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq31
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 (M.op X1 X0) X1
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq113 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 (M.op X0 (M.op X2 X2)) X1 (M.op X2 X2) (M.op X3 X3)
       have i₂ := eq24 (M.op X2 X2) X2 X3 X0
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq119 : ∀ X2 X3 : G, (M.op X2 X2) = (M.op X3 X3) := by
    intro X2 X3
    first
    | (have i₁ := eq113 x x X3 X2
       have i₂ := eq9 (M.op X3 X3) x x
       grind)
    | exact superpose eq9 eq113
    | exact resolve eq113 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq136 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq46
  have eq146 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq136 y x
       grind)
    | exact superpose eq136 eq16
    | (have j1 := eq136 y x
       grind)
    | exact resolve eq16 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq334 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1
       have i₂ := eq119 (τ X1) X0
       grind)
    | (have i₁ := eq32 X1
       have i₂ := eq119 X0 (τ X1)
       grind)
    | exact superpose eq119 eq32
    | exact resolve eq32 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq119
  have eq481 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 X1
       have i₂ := eq334 X0 X1
       grind)
    | exact superpose eq334 eq63
    | exact resolve eq63 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1048 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq146
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq146
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq146
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq146
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq146 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq1049 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq1048
  have eq5571 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1049
       grind)
    | exact superpose eq1049 eq16
    | exact resolve eq16 eq1049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq5572 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5571
       have r₂ := eq334 x (σ x)
       grind)
    | exact resolve eq5571 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5571
  have eq135427 : (σ x) = (M.op (σ y) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq63 (σ y) (σ x)
       have i₂ := eq5572
       grind)
    | exact superpose eq5572 eq63
    | exact resolve eq63 eq5572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5572
  have eq135456 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq135427
       have i₂ := eq481 y (σ y)
       grind)
    | exact superpose eq481 eq135427
    | exact resolve eq135427 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481 eq135427
  have eq135457 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq135456
  have eq199529 : y = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq63 y y
       have i₂ := eq135457
       grind)
    | exact superpose eq135457 eq63
    | exact resolve eq63 eq135457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135457
  have eq199542 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq199529
       have i₂ := eq63 y x
       grind)
    | exact superpose eq63 eq199529
    | exact resolve eq199529 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq199529
  have eq200313 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq199542
       grind)
    | exact superpose eq199542 eq16
    | exact resolve eq16 eq199542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199542
  have eq200314 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq200313
       have r₂ := eq334 x (σ x)
       grind)
    | exact resolve eq200313 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200313
  have eq200316 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq200314
       grind)
    | exact superpose eq200314 eq10
    | exact resolve eq10 eq200314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200314
  have eq200724 : x = y := by
    first
    | (have i₁ := eq200316
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq200316
    | exact resolve eq200316 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200316
  have eq200727 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq200724
       grind)
    | exact superpose eq200724 eq16
    | exact resolve eq16 eq200724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200724
  have eq200728 : False := by grind
  exact eq200728

/-- `Equation2778`: `x = ((y ◇ z) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_x_pyx_x_pyx_Equation2778 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2778 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2778.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
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
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : y ≠ (M.op x y) ∨ x = (M.op y y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq112
    | exact resolve eq112 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq767 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq94 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq7168 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7169 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq7168
    | exact resolve eq7168 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7168
  have eq7180 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq7169
       have r₂ := eq28
       grind)
    | exact resolve eq7169 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7169
  have eq7182 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq7180
    | exact resolve eq7180 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7180
  have eq7200 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq7182
  have eq7224 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq7200
    | exact resolve eq7200 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7200
  have eq7230 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq7224 eq114
    | exact resolve eq114 eq7224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7224
  have eq7238 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7230
  have eq7240 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq7238
       have r₂ := eq28
       grind)
    | exact resolve eq7238 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7238
  have eq7259 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7240
  have eq7283 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7259
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq7259
    | exact resolve eq7259 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7259
  have eq7286 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq7283
       grind)
    | exact superpose eq7283 eq72
    | exact resolve eq72 eq7283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7283
  have eq7300 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq7286
    | exact resolve eq7286 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7286
  have eq7313 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7300 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq7300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq7313
    | exact resolve eq7313 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7313
  have eq7327 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq7316
       have r₂ := eq28
       grind)
    | exact resolve eq7316 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7316
  have eq7329 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq7327
    | exact resolve eq7327 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7327
  have eq7330 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq7329
  have eq7481 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq7330
  have eq7505 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq7481
    | exact resolve eq7481 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7481
  have eq7519 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7505 eq7300
    | exact resolve eq7300 eq7505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7300 eq7505
  have eq7521 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7519
  have eq7525 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq7521
       have r₂ := eq28
       grind)
    | exact resolve eq7521 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7521
  have eq7527 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7525 eq28
    | exact resolve eq28 eq7525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7530 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7525 eq76
    | (have r₁ := eq76
       have r₂ := eq7525
       grind)
    | exact resolve eq76 eq7525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq7525
  have eq7547 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq7530
  have eq7938 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7547 eq114
    | exact resolve eq114 eq7547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7953 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq7938
  have eq7967 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq7953
       have r₂ := eq7527
       grind)
    | exact resolve eq7953 eq7527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7953
  have eq7991 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq7967
  have eq8017 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq7991
    | exact resolve eq7991 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7991
  have eq8234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8017 eq114
    | exact resolve eq114 eq8017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq8017
  have eq8246 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq8234
  have eq8250 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq8246
       have r₂ := eq28
       grind)
    | exact resolve eq8246 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8246
  have eq8269 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq8250
  have eq8293 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8269
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8269
    | exact resolve eq8269 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8269
  have eq8432 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq8293
       grind)
    | exact superpose eq8293 eq72
    | exact resolve eq72 eq8293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8293
  have eq8446 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq8432
    | exact resolve eq8432 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8432
  have eq8463 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8446 eq7547
    | exact resolve eq7547 eq8446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7547
  have eq8467 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq8463
  have eq8475 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq8467
       have r₂ := eq7527
       grind)
    | exact resolve eq8467 eq7527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7527 eq8467
  have eq8509 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq8475
  have eq8535 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq8509
    | exact resolve eq8509 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8509
  have eq8582 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8535 eq8446
    | exact resolve eq8446 eq8535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8446 eq8535
  have eq8584 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq8582
  have eq8592 : y = (M.op x y) := by
    first
    | (have r₁ := eq8584
       have r₂ := eq28
       grind)
    | exact resolve eq8584 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8584
  have eq8728 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq8592 eq21
    | exact resolve eq21 eq8592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq8735 : y ≠ y ∨ x = (M.op y y) ∨ y = (k y x) := by
    first
    | exact superpose eq8592 eq75
    | (have r₁ := eq75
       have r₂ := eq8592
       grind)
    | exact resolve eq75 eq8592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq8798 : y = (k y x) ∨ x = (M.op y y) := by grind
  clear eq8735
  have eq8849 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq8728
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8728
    | exact resolve eq8728 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8728
  have eq8850 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq8849 eq27
    | exact resolve eq27 eq8849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq10904 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq8798
       grind)
    | exact superpose eq8798 eq72
    | exact resolve eq72 eq8798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10913 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq767 x y
       have i₂ := eq8798
       grind)
    | exact superpose eq8798 eq767
    | (have j0 := eq767 x y
       grind)
    | exact resolve eq767 eq8798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8798
  have eq10916 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq10913
  have eq10923 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10916
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10916
    | exact resolve eq10916 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10916
  have eq10930 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq8849 eq10904
    | exact resolve eq10904 eq8849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10904
  have eq10932 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq8849 eq10923
    | exact resolve eq10923 eq8849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10923
  have eq10939 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10930
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10930
    | exact resolve eq10930 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10930
  have eq10940 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10932
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10932
    | exact resolve eq10932 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10932
  have eq10946 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq8849 eq10939
    | exact resolve eq10939 eq8849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10939
  have eq10947 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq8850 eq10940
    | exact resolve eq10940 eq8850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10940
  have eq10948 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq10947
       have r₂ := eq28
       grind)
    | exact resolve eq10947 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10947
  have eq10949 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10948
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10948
    | exact resolve eq10948 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10948
  have eq10950 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq8849 eq10949
    | exact resolve eq10949 eq8849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10949
  have eq10951 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10950
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10950
    | exact resolve eq10950 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10950
  have eq10999 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by grind
  clear eq10951
  have eq11032 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq8850 eq10999
    | exact resolve eq10999 eq8850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10999
  have eq11099 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq11032 eq10946
    | exact resolve eq10946 eq11032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10946 eq11032
  have eq11102 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq11099
  have eq11104 : x = (M.op y y) := by
    first
    | (have r₁ := eq11102
       have r₂ := eq28
       grind)
    | exact resolve eq11102 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11102
  have eq11136 : (M.op x y) = (k y x) := by grind
  clear eq11104
  have eq11169 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq11136
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11136
    | exact resolve eq11136 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq11136
  have eq11195 : y = (k y x) := by
    first
    | exact superpose eq8592 eq11169
    | exact resolve eq11169 eq8592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8592 eq11169
  have eq11327 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11195
       grind)
    | exact superpose eq11195 eq72
    | exact resolve eq72 eq11195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq11336 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq767 x y
       have i₂ := eq11195
       grind)
    | exact superpose eq11195 eq767
    | (have j0 := eq767 x y
       grind)
    | exact resolve eq767 eq11195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767 eq11195
  have eq11339 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq11336
  have eq11345 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq11339
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11339
    | exact resolve eq11339 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11339
  have eq11352 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq8849 eq11327
    | exact resolve eq11327 eq8849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11327
  have eq11353 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq8849 eq11345
    | exact resolve eq11345 eq8849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11345
  have eq11360 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq11352
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11352
    | exact resolve eq11352 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11352
  have eq11361 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq11353
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11353
    | exact resolve eq11353 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11353
  have eq11367 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq8849 eq11360
    | exact resolve eq11360 eq8849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11360
  have eq11368 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq8850 eq11361
    | exact resolve eq11361 eq8850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11361
  have eq11369 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq11368
       have r₂ := eq28
       grind)
    | exact resolve eq11368 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11368
  have eq11370 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq11369
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11369
    | exact resolve eq11369 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq11369
  have eq11371 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq8849 eq11370
    | exact resolve eq11370 eq8849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8849 eq11370
  have eq11372 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq11371
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11371
    | exact resolve eq11371 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq11371
  have eq12440 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq11372
  have eq12478 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq8850 eq12440
    | exact resolve eq12440 eq8850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8850 eq12440
  have eq12485 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11367 eq12478
    | exact resolve eq12478 eq11367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11367 eq12478
  have eq12488 : False := by grind
  exact eq12488

/-- `Equation2887`: `x = ((x ◇ (y ◇ z)) ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_pyy_pyy_pxy_pyx_Equation2887 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2887 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2887.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X2)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X2)) X1 X2
       have i₂ := eq9 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 X0 (σ x) (σ y)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq78 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ x)) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op (M.op X0 (M.op sF4 x)) sF4)
       have i₂ := eq9 X0 sF4 x
       grind)
    | exact superpose eq9 eq55
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq91 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq130 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq212 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X1 X2)) X1)) ≠ X0 ∨ (k X1 (M.op (M.op X0 (M.op X1 X2)) X1)) = (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op (M.op X0 (M.op X1 X2)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 (M.op X1 X2)) X1)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X1 (M.op (M.op X0 (M.op X1 X2)) X1)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq130 X0 X0
       have i₂ := eq215 X0
       grind)
    | exact superpose eq215 eq130
    | exact resolve eq130 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq229 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq215 (σ X0)
       grind)
    | exact superpose eq215 eq15
    | exact resolve eq15 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq229 X0
       have i₂ := eq215 X0
       grind)
    | exact superpose eq215 eq229
    | exact resolve eq229 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq231 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq228 X0
       have i₂ := eq215 (τ X0)
       grind)
    | exact superpose eq215 eq228
    | exact resolve eq228 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq228
  have eq315 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq78 eq9
    | exact resolve eq9 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq324 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq315 (M.op X0 (M.op sF2 x))
       have i₂ := eq9 X0 sF2 x
       grind)
    | exact superpose eq9 eq315
    | exact resolve eq315 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq581 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq596 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq58
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq58
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq601 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq596
    | exact resolve eq596 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq605 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq601
    | exact resolve eq601 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq608 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X2 X3)) X2)) = (M.op (M.op X1 (M.op X0 (M.op X2 X3))) (M.op X0 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X1 (M.op X0 (M.op X2 X3)) X2 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq54
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq625 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X2 (M.op X0 (M.op (M.op X1 X3) X4))) (M.op X0 (M.op (M.op X1 X3) X4))) = (M.op (M.op X2 (M.op (M.op (M.op X0 X1) X1) X5)) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq54 X0 (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X2) X3
       have i₂ := eq54 X0 X1 X2 X3
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq634 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op X1 X2) x
       have i₂ := eq54 X0 X1 X2 x
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op (M.op X0 X1) X1) X1) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 (M.op (M.op X1 X2) X3)) X1 X2
       have i₂ := eq54 X0 X1 X2 X3
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq650 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X0 (M.op (M.op X1 X3) X4))) (M.op X0 (M.op (M.op X1 X3) X4))) = (M.op (M.op X2 (M.op X0 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq625 X0 X1 X2 X3 X4 x
       have i₂ := eq54 X2 (M.op X0 X1) X1 x
       grind)
    | exact superpose eq54 eq625
    | exact resolve eq625 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq665 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op (M.op X0 (M.op (M.op X1 X3) X4)) (M.op X1 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq650 X0 X1 X2 X3 X4
       have i₂ := eq608 X0 X2 (M.op X1 X3) X4
       grind)
    | exact superpose eq608 eq650
    | exact resolve eq650 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq650
  have eq670 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq665 X0 X1 X2 x x
       have i₂ := eq54 X0 X1 x x
       grind)
    | exact superpose eq54 eq665
    | exact resolve eq665 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq691 : ∀ X0 : G, x = (M.op (M.op (M.op x y) y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq634 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq634
    | (have j0 := eq634 x y X0
       grind)
    | exact resolve eq634 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq692 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq634
    | (have j0 := eq634 (σ x) (σ y) X0
       grind)
    | exact resolve eq634 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq634 (M.op X0 (M.op X1 X3)) X1 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq634
    | exact resolve eq634 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq717 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X0 X2) X2)) (M.op (M.op X0 X2) X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X2) X2) (M.op X2 x)
       have i₂ := eq634 X0 X2 x
       grind)
    | exact superpose eq634 eq9
    | exact resolve eq9 eq634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq723 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X2)) (M.op (M.op (M.op X0 X2) X2) X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq717 X0 X1 X2
       have i₂ := eq670 (M.op X0 X2) X2 (M.op X1 X0)
       grind)
    | exact superpose eq670 eq717
    | exact resolve eq717 eq670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq760 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = (M.op (M.op X0 x) (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq691 eq54
    | exact resolve eq54 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq784 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq692 eq54
    | exact resolve eq54 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq842 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X1 (M.op (M.op (M.op X0 X2) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq693 X1 (M.op (M.op X0 X2) X2) X3 (M.op X2 x)
       have i₂ := eq634 X0 X2 x
       grind)
    | exact superpose eq634 eq693
    | exact resolve eq693 eq634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq904 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54 X0 X1 X2 X3
       have i₂ := eq693 (M.op X0 (M.op (M.op X1 X2) X3)) X1 X2 X4
       grind)
    | (have i₁ := eq54 X0 X1 X2 X3
       have i₂ := eq693 (M.op X0 (M.op (M.op X1 X2) X3)) X1 X4 X2
       grind)
    | exact superpose eq693 eq54
    | exact resolve eq54 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq931 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq723 X0 X1 X2
       have i₂ := eq842 X0 (M.op (M.op X1 X0) (M.op X0 X2)) X2 X2
       grind)
    | exact superpose eq842 eq723
    | exact resolve eq723 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq1568 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) (M.op (M.op x y) y)) (M.op (M.op x y) X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq760 eq634
    | exact resolve eq634 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq1744 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (σ y))) (M.op (M.op (σ x) (σ y)) X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq784 eq634
    | exact resolve eq634 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq1798 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X0 X2) X2)) = (M.op X1 (M.op (M.op X0 (M.op X2 X3)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq842 (M.op (M.op X0 X2) X2) X1 (M.op X2 X3) X4
       have i₂ := eq634 X0 X2 X3
       grind)
    | exact superpose eq634 eq842
    | exact resolve eq842 eq634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq1912 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) X1)) ≠ X0 ∨ (k X1 (M.op (M.op X0 (M.op X1 X2)) X1)) = (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op (M.op X0 (M.op X1 X2)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq212 X0 X1 X2
       have i₂ := eq1798 X0 X1 X1 X2 X1
       grind)
    | exact superpose eq1798 eq212
    | (have j0 := eq212 X0 X1 X2
       grind)
    | exact resolve eq212 eq1798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq1964 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) X1)) ≠ X0 ∨ (k X1 (M.op (M.op X0 (M.op X1 X2)) X1)) = (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1912 X0 X1 X2
       have i₂ := eq1798 X0 (M.op (M.op X0 (M.op X1 X2)) X1) X1 X2 X1
       grind)
    | exact superpose eq1798 eq1912
    | (have j0 := eq1912 X0 X1 X2
       grind)
    | exact resolve eq1912 eq1798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1798 eq1912
  have eq2177 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) (M.op (M.op x y) X1)) (M.op (M.op x y) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1568 X0 X1
       have i₂ := eq693 (M.op X0 x) sF0 y x
       grind)
    | (have i₁ := eq1568 X0 X1
       have i₂ := eq693 (M.op X0 x) sF0 X2 y
       grind)
    | exact superpose eq693 eq1568
    | exact resolve eq1568 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1568
  have eq2318 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) X1)) (M.op (M.op (σ x) (σ y)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1744 X0 X1
       have i₂ := eq693 (M.op X0 sF2) sF4 sF3 x
       grind)
    | (have i₁ := eq1744 X0 X1
       have i₂ := eq693 (M.op X0 sF2) sF4 X2 sF3
       grind)
    | exact superpose eq693 eq1744
    | exact resolve eq1744 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1744
  have eq2479 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op X0 (M.op (M.op (M.op x y) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq2177 eq634
    | exact resolve eq634 eq2177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2177
  have eq2659 : ∀ X0 X1 X2 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq2318 eq634
    | exact resolve eq634 eq2318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634 eq2318
  have eq2860 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq581 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq581
    | (have j0 := eq581 X0 X1
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq581 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq3607 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X1) ≠ (M.op X1 (M.op X0 X1)) ∨ (k X1 (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op X1 X3)) X1)) = (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op X1 X3)) X1) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1964 (M.op (M.op X0 (M.op X1 X2)) X1) X1 X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq1964
    | exact resolve eq1964 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1964
  have eq3660 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X1) ≠ (M.op X1 (M.op X0 X1)) ∨ (k X1 (M.op X0 (M.op X1 X2))) = (M.op (M.op X0 (M.op X1 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3607 X0 X0 X2 X2
       have i₂ := eq931 X0 (M.op X0 (M.op X0 X2)) X2
       grind)
    | exact superpose eq931 eq3607
    | (have j0 := eq3607 X0 X1 X2 x
       grind)
    | exact resolve eq3607 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3607
  have eq6791 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X3) X4)) = (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X1 X2)) (M.op X1 X2)) (M.op X1 X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq693 (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X1 X2)) (M.op X1 X2)) X1 X2 X5
       have i₂ := eq635 X0 (M.op X1 X2) X3 X4
       grind)
    | exact superpose eq635 eq693
    | exact resolve eq693 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635 eq693
  have eq6822 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X3) X4)) = (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op (M.op X1 X2) X2)) (M.op X1 X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq6791 X0 X1 X2 X3 X4 X5
       have i₂ := eq670 X1 X2 (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq670 eq6791
    | exact resolve eq6791 eq670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670 eq6791
  have eq6974 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X3) X4)) = (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X1) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6822 X0 X1 X2 X3 X4 x
       have i₂ := eq904 (M.op (M.op X0 (M.op X1 X2)) X1) X1 X2 X2 x
       grind)
    | exact superpose eq904 eq6822
    | exact resolve eq6822 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904 eq6822
  have eq7084 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6974 X0 X1 X2 X3 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq6974
    | exact resolve eq6974 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6974
  have eq68966 : (M.op x y) ≠ (M.op y (M.op (M.op (M.op x y) y) y)) ∨ (k y x) = (M.op x (M.op (M.op (M.op x y) y) y)) := by
    first
    | exact superpose eq691 eq3660
    | exact resolve eq3660 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq68967 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y))) ∨ (k (σ y) (σ x)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y))) := by
    first
    | exact superpose eq692 eq3660
    | exact resolve eq3660 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692 eq3660
  have eq69015 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y))) := by
    first
    | exact superpose eq2659 eq68967
    | exact resolve eq68967 eq2659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68967
  have eq69016 : (M.op x y) ≠ (M.op y x) ∨ (k y x) = (M.op x (M.op (M.op (M.op x y) y) y)) := by
    first
    | exact superpose eq2479 eq68966
    | exact resolve eq68966 eq2479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68966
  have eq69095 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y))) := by
    first
    | exact superpose eq26 eq69015
    | exact resolve eq69015 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69015
  have eq69096 : (M.op x y) ≠ (M.op y x) ∨ (k y x) = (M.op x (M.op (M.op (M.op x y) y) y)) := by
    first
    | (have i₁ := eq69016
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq69016
    | exact resolve eq69016 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69016
  have eq69141 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq2659 eq69095
    | exact resolve eq69095 eq2659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69095
  have eq69142 : (M.op x y) ≠ (M.op y x) ∨ (k y x) = (M.op x x) := by
    first
    | exact superpose eq2479 eq69096
    | exact resolve eq69096 eq2479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69096
  have eq69182 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) ∨ (σ (k y x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq58 eq69141
    | exact resolve eq69141 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69141
  have eq118875 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq2860 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2860
    | (have j0 := eq2860 x y
       grind)
    | exact resolve eq2860 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2860
  have eq118919 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq118875
    | exact resolve eq118875 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118875
  have eq118920 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq118919
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq118919
    | exact resolve eq118919 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118919
  have eq118921 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq118920
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq118920
    | exact resolve eq118920 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118920
  have eq118922 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq118921
    | exact resolve eq118921 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118921
  have eq118923 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq118922
       have r₂ := eq27
       grind)
    | exact resolve eq118922 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118922
  have eq118924 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq118923
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq118923
    | exact resolve eq118923 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118923
  have eq118925 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq118924
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq118924
    | exact resolve eq118924 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118924
  have eq118926 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq118925
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq118925
    | exact resolve eq118925 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118925
  have eq118927 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq118926
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq118926
    | exact resolve eq118926 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq118926
  have eq118928 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq118927
    | exact resolve eq118927 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118927
  have eq118973 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq118928 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq118928
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq118928
       grind)
    | exact resolve eq13 eq118928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119015 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq118928
  have eq119016 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq118973
  have eq119057 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq119016
    | exact resolve eq119016 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119016
  have eq119093 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq119057
       have r₂ := eq119015
       grind)
    | exact resolve eq119057 eq119015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119015 eq119057
  have eq119102 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq58 eq119093
    | exact resolve eq119093 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq119093
  have eq119105 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq119102
       have r₂ := eq69182
       grind)
    | exact resolve eq119102 eq69182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69182 eq119102
  have eq119118 : (k y x) = (τ (M.op (σ x) (σ x))) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq119105
       grind)
    | exact superpose eq119105 eq10
    | exact resolve eq10 eq119105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119105
  have eq119203 : (k y x) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq119118
       have i₂ := eq231 sF2
       grind)
    | exact superpose eq231 eq119118
    | exact resolve eq119118 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq119118
  have eq119229 : (k y x) = (M.op x x) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq38 eq119203
    | exact resolve eq119203 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq119203
  have eq119245 : (k y x) = (M.op x x) ∨ (M.op y x) = (M.op x x) := by
    first
    | (have r₁ := eq119229
       have r₂ := eq69142
       grind)
    | exact resolve eq119229 eq69142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119229
  have eq119288 : (M.op x y) = (M.op x x) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op y x) = (M.op x x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq119245
       grind)
    | exact superpose eq119245 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq119245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119299 : (M.op x y) = (M.op x x) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq119288
  have eq119310 : (M.op x y) = (M.op x x) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq119299
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119299
    | exact resolve eq119299 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119299
  have eq119325 : (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq119310
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119310
    | exact resolve eq119310 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119310
  have eq119599 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op X0 (M.op (M.op (M.op x x) X1) X2)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7084 X0 y x X1 X2
       have i₂ := eq119325
       grind)
    | exact superpose eq119325 eq7084
    | exact resolve eq7084 eq119325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119325
  have eq119620 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq119599 X0 x x
       have i₂ := eq7084 X0 x x x x
       grind)
    | exact superpose eq7084 eq119599
    | exact resolve eq119599 eq7084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119599
  have eq269206 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op x y) X1) X2)) = (M.op X0 y) ∨ (M.op X3 x) = (M.op X3 y) ∨ (M.op x y) = (M.op x x) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7084 X0 y x X1 X2
       have i₂ := eq119620 X3
       grind)
    | (have i₁ := eq7084 X0 X0 x X3 x
       have i₂ := eq119620 X0
       grind)
    | exact superpose eq119620 eq7084
    | (have j1 := eq119620 X3
       grind)
    | exact resolve eq7084 eq119620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119620
  have eq269209 : ∀ X0 X3 : G, (M.op X0 x) = (M.op X0 y) ∨ (M.op X3 x) = (M.op X3 y) ∨ (M.op x y) = (M.op x x) := by
    intro X0 X3
    first
    | exact superpose eq2479 eq269206
    | (have j0 := eq269206 X0 x x X0
       grind)
    | exact resolve eq269206 eq2479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479 eq269206
  have eq1118544 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 x) ∨ (M.op X0 x) = (M.op X0 y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq269209 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269209
  have eq1118545 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1118544 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118544
  have eq1120187 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1118545 x
       grind)
    | exact superpose eq1118545 eq18
    | (have j1 := eq1118545 x
       grind)
    | exact resolve eq18 eq1118545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1118545
  have eq1120514 : (M.op x y) = (M.op x x) := by grind
  clear eq1120187
  have eq1120831 : (M.op x y) = (k y x) ∨ (M.op x y) ≠ (M.op y x) := by
    first
    | (have i₁ := eq69142
       have i₂ := eq1120514
       grind)
    | exact superpose eq1120514 eq69142
    | exact resolve eq69142 eq1120514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69142
  have eq1120973 : (M.op x y) = (k y x) ∨ (M.op y x) = (M.op x x) := by
    first
    | (have i₁ := eq119245
       have i₂ := eq1120514
       grind)
    | exact superpose eq1120514 eq119245
    | exact resolve eq119245 eq1120514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119245
  have eq1124564 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1120973
       have i₂ := eq1120514
       grind)
    | exact superpose eq1120514 eq1120973
    | exact resolve eq1120973 eq1120514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120973
  have eq1125038 : (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq1124564
       have r₂ := eq1120831
       grind)
    | exact resolve eq1124564 eq1120831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120831 eq1124564
  have eq1125266 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq605
       have i₂ := eq1125038
       grind)
    | exact superpose eq1125038 eq605
    | exact resolve eq605 eq1125038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605 eq1125038
  have eq1125348 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq1125266
    | exact resolve eq1125266 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125266
  have eq1125362 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq1125348
       have r₂ := eq27
       grind)
    | exact resolve eq1125348 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125348
  have eq1133311 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq230 x
       have i₂ := eq1120514
       grind)
    | exact superpose eq1120514 eq230
    | exact resolve eq230 eq1120514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq1120514
  have eq1133684 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1133311
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1133311
    | exact resolve eq1133311 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1133311
  have eq1134093 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq1133684
    | exact resolve eq1133684 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1133684
  have eq1137611 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1134093 eq1125362
    | exact resolve eq1125362 eq1134093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125362
  have eq1137890 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1134093 eq324
    | exact resolve eq324 eq1134093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1138045 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq1134093 eq931
    | exact resolve eq931 eq1134093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1140012 : (σ x) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq324 eq1138045
    | (have j0 := eq1138045 (σ y)
       grind)
    | exact resolve eq1138045 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138045
  have eq1141122 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op X0 (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq1137890 eq324
    | exact resolve eq324 eq1137890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq1148546 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq1137890 eq1140012
    | exact resolve eq1140012 eq1137890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137890 eq1140012
  have eq1169658 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X1) X2)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1137611 eq7084
    | exact resolve eq7084 eq1137611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7084 eq1137611
  have eq1169696 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq2659 eq1169658
    | exact resolve eq1169658 eq2659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2659 eq1169658
  have eq1188698 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) X0)) (σ x)) ∨ (M.op X1 (σ x)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1169696 eq931
    | (have j1 := eq1169696 X1
       grind)
    | exact resolve eq931 eq1169696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931 eq1169696
  have eq1188750 : ∀ X1 : G, (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ (M.op X1 (σ x)) = (M.op X1 (σ y)) := by
    intro X1
    first
    | exact superpose eq1141122 eq1188698
    | (have j0 := eq1188698 x X1
       grind)
    | exact resolve eq1188698 eq1141122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141122 eq1188698
  have eq1188785 : ∀ X1 : G, (M.op X1 (σ x)) = (M.op X1 (σ y)) ∨ (σ x) = (σ y) := by
    intro X1
    first
    | exact superpose eq1148546 eq1188750
    | (have j0 := eq1188750 X1
       grind)
    | exact resolve eq1188750 eq1148546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148546 eq1188750
  have eq1189187 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1188785 eq26
    | (have j1 := eq1188785 (σ x)
       grind)
    | exact resolve eq26 eq1188785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188785
  have eq1189256 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1134093 eq1189187
    | exact resolve eq1189187 eq1134093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189187
  have eq1189276 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1189256
       have r₂ := eq27
       grind)
    | exact resolve eq1189256 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189256
  have eq1189279 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1189276 eq26
    | exact resolve eq26 eq1189276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1189276
  have eq1197398 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1134093 eq1189279
    | exact resolve eq1189279 eq1134093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134093 eq1189279
  have eq1206920 : False := by grind
  exact eq1206920

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_x_y_pxy_pxy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq50
    | exact resolve eq50 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
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
  clear eq66 eq70
  have eq97 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq97
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq97 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
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
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq21 eq112
    | exact resolve eq112 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
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
  have eq13920 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13921 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq13920
    | exact resolve eq13920 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13920
  have eq13932 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq13921
       have r₂ := eq28
       grind)
    | exact resolve eq13921 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13921
  have eq13936 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq13932
    | exact resolve eq13932 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13932
  have eq13938 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq13936 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq13936
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq13936
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq13936
       grind)
    | exact resolve eq13 eq13936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13936
  have eq13956 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq13938
       have r₂ := eq27
       grind)
    | exact resolve eq13938 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13938
  have eq14161 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq13956 eq114
    | exact resolve eq114 eq13956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq13956
  have eq14170 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq14161
  have eq14173 : (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq14170
       have r₂ := eq28
       grind)
    | exact resolve eq14170 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14170
  have eq14175 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq14173
       grind)
    | exact superpose eq14173 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq14173
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq14173
       grind)
    | exact resolve eq13 eq14173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14173
  have eq14193 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq14175
       have r₂ := eq19
       grind)
    | exact resolve eq14175 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14175
  have eq14511 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq14193
       grind)
    | exact superpose eq14193 eq97
    | exact resolve eq97 eq14193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq14193
  have eq14527 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq14511
    | exact resolve eq14511 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14511
  have eq14883 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq14527 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq14527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14884 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y := by grind
  clear eq14883
  have eq14888 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq27 eq14884
    | exact resolve eq14884 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14884
  have eq14899 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq14888
       have r₂ := eq28
       grind)
    | exact resolve eq14888 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14888
  have eq14903 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq14899
    | exact resolve eq14899 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14899
  have eq14931 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq14903 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq14903
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq14903
       grind)
    | exact resolve eq13 eq14903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14903
  have eq14949 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq14931
       have r₂ := eq27
       grind)
    | exact resolve eq14931 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14931
  have eq15238 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq14949 eq14527
    | exact resolve eq14527 eq14949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14527 eq14949
  have eq15241 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq15238
  have eq15246 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq15241
       have r₂ := eq28
       grind)
    | exact resolve eq15241 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15241
  have eq15249 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq15246 eq30
    | exact resolve eq30 eq15246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq15246
  have eq15366 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq15249
    | exact resolve eq15249 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq15249
  have eq15367 : x = y := by grind
  clear eq15366
  have eq15662 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq15367
       grind)
    | exact superpose eq15367 eq19
    | exact resolve eq19 eq15367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq15663 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq15367
       grind)
    | exact superpose eq15367 eq25
    | exact resolve eq25 eq15367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq15367
  have eq15777 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq15663
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15663
    | exact resolve eq15663 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq15663
  have eq15792 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq15777 eq27
    | exact resolve eq27 eq15777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq15777
  have eq16786 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq15792 eq71
    | exact resolve eq71 eq15792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq15792
  have eq16846 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16786
       have i₂ := eq15662
       grind)
    | exact superpose eq15662 eq16786
    | exact resolve eq16786 eq15662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15662 eq16786
  have eq16859 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16846 eq15
    | exact resolve eq15 eq16846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16846
  have eq16903 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq16859
    | exact resolve eq16859 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq16859
  have eq16912 : False := by grind
  exact eq16912
