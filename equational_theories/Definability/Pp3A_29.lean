import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pxx_pyy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq175 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq16 X0 X2 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq16 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq177 X0 X0
       grind)
    | exact superpose eq177 eq178
    | exact resolve eq178 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq178
  have eq184 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq665 : (M.op y y) = (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) := by
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
  have eq673 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq760 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq761 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq760 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq760 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq760 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (M.op x x)) x
       grind)
    | (have r₁ := eq760 x
       have r₂ := eq13 (k x x) x
       grind)
    | exact resolve eq760 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq770 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq179 X0
       have i₂ := eq761 X0
       grind)
    | exact superpose eq761 eq179
    | exact resolve eq179 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq1867 : ∀ X0 X1 X2 : G, y = (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X2 (M.op x x))) ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X2 X0 X1 y
       have i₂ := eq665
       grind)
    | exact superpose eq665 eq176
    | exact resolve eq176 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq1891 : x = y ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1867 x x x
       have i₂ := eq176 x x x x
       grind)
    | exact superpose eq176 eq1867
    | exact resolve eq1867 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq1867
  have eq1911 : (M.op x y) = (k y x) ∨ x = y ∨ y = (k x x) := by
    first
    | (have i₁ := eq1891
       have i₂ := eq761 x
       grind)
    | exact superpose eq761 eq1891
    | exact resolve eq1891 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1891
  have eq4284 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X0 (M.op (σ x) (σ x)))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq673 eq184
    | exact resolve eq184 eq673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq4315 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq184 eq4284
    | exact resolve eq4284 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq4284
  have eq4343 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4315
       have i₂ := eq761 sF2
       grind)
    | exact superpose eq761 eq4315
    | exact resolve eq4315 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4315
  have eq4564 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (k x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1911
       grind)
    | exact superpose eq1911 eq39
    | exact resolve eq39 eq1911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1911
  have eq4566 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (k x x) := by
    first
    | (have i₁ := eq4564
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4564
    | exact resolve eq4564 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4564
  have eq4568 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (k x x) := by
    first
    | exact superpose eq20 eq4566
    | exact resolve eq4566 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4566
  have eq16110 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ y = (k x x) := by
    first
    | exact superpose eq4568 eq4343
    | exact resolve eq4343 eq4568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4343 eq4568
  have eq16119 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x x) := by
    first
    | (have r₁ := eq16110
       have r₂ := eq27
       grind)
    | exact resolve eq16110 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16110
  have eq16126 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x x) := by
    first
    | exact superpose eq16119 eq97
    | exact resolve eq97 eq16119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq16119
  have eq16213 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x x) := by
    first
    | exact superpose eq31 eq16126
    | exact resolve eq16126 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16126
  have eq16214 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq16213
  have eq16233 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq16214
       grind)
    | exact superpose eq16214 eq39
    | exact resolve eq39 eq16214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16237 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq770 x
       have i₂ := eq16214
       grind)
    | exact superpose eq16214 eq770
    | exact resolve eq770 eq16214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16214
  have eq16303 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16237
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16237
    | exact resolve eq16237 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16237
  have eq16307 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16233
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16233
    | exact resolve eq16233 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16233
  have eq16330 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16307
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16307
    | exact resolve eq16307 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16307
  have eq16413 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq16303
       grind)
    | exact superpose eq16303 eq39
    | exact resolve eq39 eq16303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16303
  have eq16415 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16413
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16413
    | exact resolve eq16413 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16413
  have eq16417 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq16415
    | exact resolve eq16415 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16415
  have eq16487 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16330 eq770
    | exact resolve eq770 eq16330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq16330
  have eq16561 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq16487
    | exact resolve eq16487 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16487
  have eq16577 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16417 eq16561
    | exact resolve eq16561 eq16417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16417 eq16561
  have eq16590 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq16577
       have r₂ := eq27
       grind)
    | exact resolve eq16577 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16577
  have eq16598 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq16590 eq31
    | exact resolve eq31 eq16590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq16590
  have eq16717 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq16598
    | exact resolve eq16598 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq16598
  have eq16718 : x = y := by grind
  clear eq16717
  have eq16725 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq16718
       grind)
    | exact superpose eq16718 eq18
    | exact resolve eq18 eq16718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq16726 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq16718
       grind)
    | exact superpose eq16718 eq24
    | exact resolve eq24 eq16718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq16718
  have eq16759 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq16726
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16726
    | exact resolve eq16726 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16726
  have eq16760 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq16725
       have i₂ := eq761 x
       grind)
    | exact superpose eq761 eq16725
    | exact resolve eq16725 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16725
  have eq16761 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq16759 eq26
    | exact resolve eq26 eq16759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq16759
  have eq16880 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq16761
       have i₂ := eq761 sF2
       grind)
    | exact superpose eq761 eq16761
    | exact resolve eq16761 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761 eq16761
  have eq16894 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq16760
       grind)
    | exact superpose eq16760 eq39
    | exact resolve eq39 eq16760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq16760
  have eq16972 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq16894
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16894
    | exact resolve eq16894 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq16894
  have eq16990 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16880 eq16972
    | exact resolve eq16972 eq16880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16880 eq16972
  have eq17000 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq16990
    | exact resolve eq16990 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq16990
  have eq17006 : False := by grind
  exact eq17006

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq55 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq57 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq23
  have eq58 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X2) (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq55
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (k (M.op X1 (M.op X0 X1)) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X3 (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) X3 X2
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq55 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq55
    | exact resolve eq55 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq9
    | exact resolve eq9 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
       have i₂ := eq65 (M.op X0 X0)
       grind)
    | exact superpose eq65 eq9
    | exact resolve eq9 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq55 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq55 eq68
    | exact resolve eq68 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq72 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq71
    | exact resolve eq71 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq79 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (M.op X0 X0) X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq58
    | exact resolve eq58 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq72
  have eq96 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq96 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq96
    | (have j0 := eq96 (σ X0)
       grind)
    | exact resolve eq96 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X1 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X0 X0))
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq9
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq66 X1 X1
       grind)
    | exact superpose eq66 eq79
    | exact resolve eq79 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq79
  have eq262 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X0 (M.op X0 X0) X2 X1
       have i₂ := eq127 X0 X0
       grind)
    | exact superpose eq127 eq63
    | exact resolve eq63 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 (M.op X1 X2) (M.op X0 (M.op X1 X2)) X1 X2
       have i₂ := eq63 X0 (M.op X1 X2) X0 (M.op X1 X2)
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq262 (M.op X0 X1) X2 X3
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq262
    | exact resolve eq262 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 X2) X1)) = (M.op X4 (M.op (M.op X3 X4) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq262 X1 X4 X3
       have i₂ := eq262 X1 X2 X0
       grind)
    | exact superpose eq262 eq262
    | exact resolve eq262 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 X2 X3 : G, (M.op X3 (M.op X3 X3)) = (M.op (M.op X2 (M.op X0 X0)) (M.op X0 X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq262 X3 (M.op X2 (M.op X0 X0)) (M.op x (M.op X2 X2))
       have i₂ := eq126 x X2 X0
       grind)
    | exact superpose eq126 eq262
    | exact resolve eq262 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X2 (M.op (M.op X0 X2) X1))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq127 X1 X3
       have i₂ := eq262 X1 X2 X0
       grind)
    | exact superpose eq262 eq127
    | exact resolve eq127 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X2) X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X1
       have i₂ := eq262 X1 X2 X0
       grind)
    | exact superpose eq262 eq60
    | exact resolve eq60 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq303 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X1 X1)) (M.op X2 (M.op (M.op X0 X2) X1))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq126 X3 X1 X1
       have i₂ := eq262 X1 X2 X0
       grind)
    | exact superpose eq262 eq126
    | exact resolve eq126 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op (M.op X0 X2) X1)) (M.op X1 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq126 X1 X1 X3
       have i₂ := eq262 X1 X2 X0
       grind)
    | exact superpose eq262 eq126
    | exact resolve eq126 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq309 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X1 (M.op X1 X1)))) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 (M.op X0 X1) X1 X3 X2
       have i₂ := eq262 X1 X1 X0
       grind)
    | exact superpose eq262 eq63
    | exact resolve eq63 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq316 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq309 X0 X1 x x
       have i₂ := eq63 X1 X1 x x
       grind)
    | exact superpose eq63 eq309
    | exact resolve eq309 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq317 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op X1 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq288 X0 X1 X2 X3
       have i₂ := eq265 X1 X0 X1
       grind)
    | exact superpose eq265 eq288
    | exact resolve eq288 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq377 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq384 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq377 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq398 : ∀ X0 X2 X3 : G, (M.op X3 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq302 (M.op x (M.op X2 X2)) X3 (M.op X2 (M.op X0 X0))
       have i₂ := eq126 x X2 X0
       grind)
    | exact superpose eq126 eq302
    | exact resolve eq302 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq401 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X1 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq302 X0 (M.op X0 X1) X1
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq302
    | exact resolve eq302 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X1)) X1) = (M.op (M.op (M.op X2 (M.op X0 X1)) X1) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq302 X0 (M.op (M.op X2 (M.op X0 X1)) X1) X1
       have i₂ := eq302 X2 X1 (M.op X0 X1)
       grind)
    | exact superpose eq302 eq302
    | exact resolve eq302 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq410 X0 X1 X2
       have i₂ := eq316 (M.op X2 (M.op X0 X1)) X1
       grind)
    | exact superpose eq316 eq410
    | exact resolve eq410 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq504 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op (M.op X2 (M.op X0 X0)) (M.op X0 X3))) = X3 := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq301 (M.op x (M.op X2 X2)) X3 (M.op X2 (M.op X0 X0)) X4
       have i₂ := eq126 x X2 X0
       grind)
    | exact superpose eq126 eq301
    | exact resolve eq301 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) = (M.op (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq302 X0 (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) (M.op X1 X2)
       have i₂ := eq301 X3 X2 (M.op X0 (M.op X1 X2)) X1
       grind)
    | exact superpose eq301 eq302
    | exact resolve eq302 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq521 X0 X1 X2 X3
       have i₂ := eq316 (M.op X3 (M.op X0 (M.op X1 X2))) X2
       grind)
    | exact superpose eq316 eq521
    | exact resolve eq521 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq646 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 (M.op (M.op X1 X0) X2)) (M.op X0 (M.op (M.op X1 X0) X2))) = (M.op (M.op X5 (M.op X4 X2)) (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq539 X4 (M.op x X2) (M.op X0 (M.op (M.op X1 X0) X2)) X5
       have i₂ := eq301 X1 X2 X0 x
       grind)
    | exact superpose eq301 eq539
    | exact resolve eq539 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : ∀ X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op X1 X2)) = (M.op (M.op X3 X2) (M.op X1 X2)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq539 X2 (M.op x (M.op X1 X1)) (M.op X1 X2) X3
       have i₂ := eq398 X1 x X2
       grind)
    | exact superpose eq398 eq539
    | exact resolve eq539 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq657 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) = (M.op (M.op X4 X2) (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq539 (M.op x X2) X0 (M.op (M.op X1 X0) X2) X4
       have i₂ := eq301 X1 X2 X0 x
       grind)
    | exact superpose eq301 eq539
    | exact resolve eq539 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq692 : ∀ X0 X1 X2 X4 : G, (M.op X2 (M.op (M.op X1 X0) X2)) = (M.op (M.op X4 X2) (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq657 X0 X1 X2 X4
       have i₂ := eq55 (M.op X1 X0) X2
       grind)
    | exact superpose eq55 eq657
    | exact resolve eq657 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq697 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X1 X2)) = (M.op (M.op X3 X2) (M.op X1 X2)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq649 X1 X2 X3
       have i₂ := eq55 X1 X2
       grind)
    | exact superpose eq55 eq649
    | exact resolve eq649 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq700 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X0 (M.op (M.op X1 X0) X2))) = (M.op (M.op X5 (M.op X4 X2)) (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq646 X0 X1 X2 X4 X5
       have i₂ := eq55 X0 (M.op (M.op X1 X0) X2)
       grind)
    | exact superpose eq55 eq646
    | exact resolve eq646 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq715 : ∀ X0 X1 X2 X4 X5 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = (M.op (M.op X5 (M.op X4 X2)) (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq700 X0 X1 X2 X4 X5
       have i₂ := eq265 X0 (M.op X1 X0) X2
       grind)
    | exact superpose eq265 eq700
    | exact resolve eq700 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq723 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X5 (M.op X4 X2)) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq715 X0 X1 X2 X4 X5
       have i₂ := eq302 X1 X2 X0
       grind)
    | exact superpose eq302 eq715
    | exact resolve eq715 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq871 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq384 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq384
    | (have j0 := eq384 (σ X0) (σ X1)
       grind)
    | exact resolve eq384 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq1196 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X2 X2) X0) = (M.op X4 (M.op (M.op X3 X4) (M.op X2 (M.op X0 X0)))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq289 X3 (M.op X2 (M.op X0 X0)) X4 x (M.op X2 X2)
       have i₂ := eq126 x X2 X0
       grind)
    | exact superpose eq126 eq289
    | exact resolve eq289 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1199 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 X1) = (M.op X5 (M.op (M.op X4 X5) (M.op (M.op X0 (M.op X2 X3)) (M.op X1 X1)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq289 X4 (M.op (M.op X0 (M.op X2 X3)) (M.op X1 X1)) X5 X2 X3
       have i₂ := eq9 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq9 eq289
    | exact resolve eq289 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1205 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X1 (M.op X1 X1))) = (M.op X5 (M.op (M.op X4 X5) (M.op (M.op X0 (M.op X2 X3)) X1))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq289 X4 (M.op (M.op X0 (M.op X2 X3)) X1) X5 X2 X3
       have i₂ := eq262 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq262 eq289
    | exact resolve eq289 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq1318 : ∀ X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X2 (M.op X2 X2)) (M.op X3 X3))) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X1 X2) (M.op x (M.op X1 X1))
       have i₂ := eq299 X1 x X2
       grind)
    | exact superpose eq299 eq9
    | exact resolve eq9 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq1400 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X0 (M.op X1 (M.op X2 X2)))) X2) = (M.op (M.op (M.op X3 (M.op X0 (M.op X1 (M.op X2 X2)))) X2) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq302 X0 (M.op (M.op X3 (M.op X0 (M.op X1 (M.op X2 X2)))) X2) (M.op X1 (M.op X2 X2))
       have i₂ := eq303 X3 X2 (M.op X0 (M.op X1 (M.op X2 X2))) X1
       grind)
    | exact superpose eq303 eq302
    | exact resolve eq302 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302 eq303
  have eq1427 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = (M.op (M.op X3 (M.op X0 (M.op X1 (M.op X2 X2)))) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1400 X0 X1 X2 X3
       have i₂ := eq316 (M.op X3 (M.op X0 (M.op X1 (M.op X2 X2)))) X2
       grind)
    | exact superpose eq316 eq1400
    | exact resolve eq1400 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq1716 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X1)) = (M.op X3 (M.op (M.op X2 X3) (M.op X1 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq289 X2 (M.op X1 (M.op X1 (M.op X0 X1))) X3 X0 X1
       have i₂ := eq401 X0 X1
       grind)
    | exact superpose eq401 eq289
    | exact resolve eq289 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq2278 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 (M.op X3 X0))) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1427 X0 X1 (M.op X2 (M.op X2 X2)) X3
       have i₂ := eq126 X2 X2 X2
       grind)
    | exact superpose eq126 eq1427
    | exact resolve eq1427 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1427
  have eq2653 : ∀ X0 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2)) = (M.op (M.op X4 X2) (M.op X3 (M.op (M.op X5 X3) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2))))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq723 X3 X5 (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2)) (M.op x X0) X4
       have i₂ := eq1318 x X0 X2
       grind)
    | exact superpose eq1318 eq723
    | exact resolve eq723 eq1318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2681 : ∀ X1 X2 X4 X5 : G, (M.op X1 X2) = (M.op X2 (M.op X4 (M.op (M.op X5 X4) (M.op X1 X2)))) := by
    intro X1 X2 X4 X5
    first
    | (have i₁ := eq723 X4 X5 (M.op X1 X2) (M.op x (M.op X1 X1)) (M.op x X2)
       have i₂ := eq504 X1 x X2 x
       grind)
    | exact superpose eq504 eq723
    | exact resolve eq723 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq2821 : ∀ X0 X2 X4 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2)) = (M.op (M.op X4 X2) (M.op X0 X2)) := by
    intro X0 X2 X4
    first
    | (have i₁ := eq2653 X0 X2 x X4 x
       have i₂ := eq1199 X0 X2 X0 X0 x x
       grind)
    | exact superpose eq1199 eq2653
    | exact resolve eq2653 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199 eq2653
  have eq2831 : ∀ X0 X2 : G, (M.op X2 (M.op X0 X2)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq2821 X0 X2 x
       have i₂ := eq697 X0 X2 x
       grind)
    | exact superpose eq697 eq2821
    | exact resolve eq2821 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2821
  have eq2907 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2)) = (M.op (M.op X4 (M.op X3 X2)) (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2)) (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2)) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2))))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq2278 (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2)) X4 X3 (M.op x X0)
       have i₂ := eq1318 x X0 X2
       grind)
    | exact superpose eq1318 eq2278
    | exact resolve eq2278 eq1318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318 eq2278
  have eq3028 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2)) = (M.op (M.op X4 (M.op X3 X2)) (M.op (M.op X2 X2) (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2)) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2))))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq2907 X0 X2 X3 X4
       have i₂ := eq265 (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2)) (M.op X0 (M.op X0 X0)) (M.op X2 X2)
       grind)
    | exact superpose eq265 eq2907
    | exact resolve eq2907 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2907
  have eq3071 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2)) = (M.op (M.op X4 (M.op X3 X2)) (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) X2)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq3028 X0 X2 X3 X4
       have i₂ := eq1196 X2 (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)) (M.op X2 X2)
       grind)
    | exact superpose eq1196 eq3028
    | exact resolve eq3028 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196 eq3028
  have eq3092 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2)) = (M.op (M.op X4 (M.op X3 X2)) (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) X2)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq3071 X0 X2 X3 X4
       have i₂ := eq55 X0 (M.op X0 X0)
       grind)
    | exact superpose eq55 eq3071
    | exact resolve eq3071 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3071
  have eq3100 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2)) = (M.op (M.op X4 (M.op X3 X2)) (M.op X0 X2)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq3092 X0 X2 X3 X4
       have i₂ := eq127 X0 X0
       grind)
    | exact superpose eq127 eq3092
    | exact resolve eq3092 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq3092
  have eq3106 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X0 X2)) = (M.op (M.op X4 (M.op X3 X2)) (M.op X0 X2)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq3100 X0 X2 X3 X4
       have i₂ := eq2831 X0 X2
       grind)
    | exact superpose eq2831 eq3100
    | exact resolve eq3100 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2831 eq3100
  have eq3183 : ∀ X0 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X2 X2) X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq2681 X2 (M.op X0 X0) (M.op X2 X2) x
       have i₂ := eq126 x X2 X0
       grind)
    | exact superpose eq126 eq2681
    | exact resolve eq2681 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq3192 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X3)) (M.op X1 X1)) = (M.op (M.op X1 X1) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2681 (M.op X0 (M.op X2 X3)) (M.op X1 X1) X3 X2
       have i₂ := eq9 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq9 eq2681
    | exact resolve eq2681 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3193 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X1 X2)) (M.op X4 (M.op X0 X4))) = (M.op (M.op X4 (M.op X0 X4)) (M.op X2 (M.op X0 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2681 (M.op X3 (M.op X1 X2)) (M.op X4 (M.op X0 X4)) X2 X1
       have i₂ := eq63 X0 X4 X3 (M.op X1 X2)
       grind)
    | exact superpose eq63 eq2681
    | exact resolve eq2681 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq2681
  have eq3290 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X1 X2)) (M.op X4 (M.op X0 X4))) = (M.op (M.op X0 X4) (M.op X2 (M.op X0 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3193 X0 X1 X2 X3 X4
       have i₂ := eq697 X2 (M.op X0 X4) X4
       grind)
    | exact superpose eq697 eq3193
    | exact resolve eq3193 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3193
  have eq3291 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X3)) (M.op X1 X1)) = (M.op X1 (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3192 X0 X1 X2 X3
       have i₂ := eq697 X3 X1 X1
       grind)
    | exact superpose eq697 eq3192
    | exact resolve eq3192 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3192
  have eq3298 : ∀ X0 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op X0 (M.op (M.op X2 X2) X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq3183 X0 X2
       have i₂ := eq692 X2 X2 X0 X0
       grind)
    | exact superpose eq692 eq3183
    | exact resolve eq3183 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692 eq3183
  have eq3320 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X1 X2)) (M.op X4 (M.op X0 X4))) = (M.op X4 (M.op X2 (M.op X0 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3290 X0 X1 X2 X3 X4
       have i₂ := eq265 X2 X0 X4
       grind)
    | exact superpose eq265 eq3290
    | exact resolve eq3290 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3290
  have eq3502 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X2)) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3298 X2 (M.op X1 X0)
       have i₂ := eq697 X1 X0 X1
       grind)
    | exact superpose eq697 eq3298
    | exact resolve eq3298 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq3507 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2)) X2) = (M.op X2 (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2)) (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3298 (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2)) X2
       have i₂ := eq504 X1 X0 X2 X2
       grind)
    | exact superpose eq504 eq3298
    | exact resolve eq3298 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq3562 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) (M.op (M.op (M.op X0 X0) (M.op X1 X2)) (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq304 X1 (M.op (M.op X0 X0) (M.op X1 X2)) X2 X3
       have i₂ := eq3298 (M.op X1 X2) X0
       grind)
    | exact superpose eq3298 eq304
    | exact resolve eq304 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq3298
  have eq3567 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) (M.op X3 (M.op X2 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3562 X0 X1 X2 X3
       have i₂ := eq3291 (M.op X0 X0) X3 X1 X2
       grind)
    | exact superpose eq3291 eq3562
    | exact resolve eq3562 eq3291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3291 eq3562
  have eq3598 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2)) X2) = (M.op X2 (M.op (M.op X1 X2) (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3507 X0 X1 X2
       have i₂ := eq55 (M.op X0 (M.op X1 X1)) (M.op X1 X2)
       grind)
    | exact superpose eq55 eq3507
    | exact resolve eq3507 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3507
  have eq3602 : ∀ X1 X2 X3 : G, (M.op X3 (M.op (M.op (M.op X1 X2) (M.op X1 X2)) (M.op X2 X3))) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq3567 x X1 X2 X3
       have i₂ := eq3320 X2 x (M.op (M.op X1 X2) (M.op X1 X2)) X2 X3
       grind)
    | exact superpose eq3320 eq3567
    | exact resolve eq3567 eq3320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3320 eq3567
  have eq3619 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2)) X2) = (M.op X1 (M.op (M.op X1 X2) (M.op (M.op X1 X2) (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3598 X0 X1 X2
       have i₂ := eq1205 X0 (M.op X1 X2) X1 X1 X1 X2
       grind)
    | exact superpose eq1205 eq3598
    | exact resolve eq3598 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205 eq3598
  have eq3621 : ∀ X1 X2 X3 : G, (M.op X3 (M.op (M.op X2 (M.op X1 X2)) (M.op X2 X3))) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq3602 X1 X2 X3
       have i₂ := eq55 X1 X2
       grind)
    | exact superpose eq55 eq3602
    | exact resolve eq3602 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3602
  have eq3627 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2)) X2) = (M.op X1 (M.op X2 (M.op (M.op X1 X2) (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3619 X0 X1 X2
       have i₂ := eq265 (M.op X1 X2) X1 X2
       grind)
    | exact superpose eq265 eq3619
    | exact resolve eq3619 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq3619
  have eq3632 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2)) X2) = (M.op X1 (M.op X2 (M.op X2 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3627 X0 X1 X2
       have i₂ := eq317 X1 X2 X2 X1
       grind)
    | exact superpose eq317 eq3627
    | exact resolve eq3627 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317 eq3627
  have eq3634 : ∀ X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X2 (M.op X2 (M.op X1 X2)))) := by
    intro X1 X2
    first
    | (have i₁ := eq3632 x X1 X2
       have i₂ := eq420 X1 X2 (M.op x (M.op X1 X1))
       grind)
    | exact superpose eq420 eq3632
    | exact resolve eq3632 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420 eq3632
  have eq4060 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X2)) (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X2))) = (M.op X2 (M.op (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X2)) (M.op (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X2)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3634 X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X2))
       have i₂ := eq3621 X1 X0 X2
       grind)
    | exact superpose eq3621 eq3634
    | exact resolve eq3634 eq3621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3621
  have eq4063 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2)) (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2))) = (M.op X2 (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2)) (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3634 X2 (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2))
       have i₂ := eq398 X1 X0 X2
       grind)
    | exact superpose eq398 eq3634
    | exact resolve eq3634 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq4137 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X0 X0)) = (M.op X4 (M.op (M.op X3 X4) (M.op X0 (M.op X0 (M.op (M.op X1 X2) X0))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq289 X3 (M.op X0 (M.op X0 (M.op (M.op X1 X2) X0))) X4 X1 X2
       have i₂ := eq3634 (M.op X1 X2) X0
       grind)
    | exact superpose eq3634 eq289
    | exact resolve eq289 eq3634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq3634
  have eq4146 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4137 X0 X1 X2 x x
       have i₂ := eq1716 (M.op X1 X2) X0 x x
       grind)
    | exact superpose eq1716 eq4137
    | exact resolve eq4137 eq1716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1716 eq4137
  have eq4199 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2)) (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2))) = (M.op X2 (M.op X2 (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4063 X0 X1 X2
       have i₂ := eq3106 (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2)) X2 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq3106 eq4063
    | exact resolve eq4063 eq3106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4063
  have eq4202 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X2)) (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X2))) = (M.op X2 (M.op X2 (M.op (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X2)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4060 X0 X1 X2
       have i₂ := eq3106 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X2)) X2 X0 (M.op X0 (M.op X1 X0))
       grind)
    | exact superpose eq3106 eq4060
    | exact resolve eq4060 eq3106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4060
  have eq4243 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X1 X2) (M.op X2 X2))) = (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2)) (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4199 X0 X1 X2
       have i₂ := eq4146 X2 (M.op X0 (M.op X1 X1)) (M.op X1 X2)
       grind)
    | exact superpose eq4146 eq4199
    | exact resolve eq4199 eq4146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4199
  have eq4246 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X2)) (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X2))) = (M.op X2 (M.op (M.op X0 X2) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4202 X0 X1 X2
       have i₂ := eq4146 X2 (M.op X0 (M.op X1 X0)) (M.op X0 X2)
       grind)
    | exact superpose eq4146 eq4202
    | exact resolve eq4202 eq4146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4202
  have eq4270 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X1 X2) (M.op X2 X2))) = (M.op (M.op X1 X2) (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4243 X0 X1 X2
       have i₂ := eq55 (M.op X0 (M.op X1 X1)) (M.op X1 X2)
       grind)
    | exact superpose eq55 eq4243
    | exact resolve eq4243 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4243
  have eq4273 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X2)) (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4246 X0 X1 X2
       have i₂ := eq9 X2 X2 X0
       grind)
    | exact superpose eq9 eq4246
    | exact resolve eq4246 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4246
  have eq4282 : ∀ X1 X2 : G, (M.op X2 (M.op (M.op X1 X2) (M.op X2 X2))) = (M.op (M.op X1 X1) (M.op (M.op X1 X2) (M.op X1 X2))) := by
    intro X1 X2
    first
    | (have i₁ := eq4270 x X1 X2
       have i₂ := eq4146 (M.op X1 X2) x (M.op X1 X1)
       grind)
    | exact superpose eq4146 eq4270
    | exact resolve eq4270 eq4146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4146 eq4270
  have eq4285 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4273 X0 X1 X2
       have i₂ := eq55 (M.op X0 (M.op X1 X0)) (M.op X0 X2)
       grind)
    | exact superpose eq55 eq4273
    | exact resolve eq4273 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4273
  have eq4289 : ∀ X1 X2 : G, (M.op X2 (M.op (M.op X1 X2) (M.op X2 X2))) = (M.op (M.op X1 X1) (M.op X2 (M.op X1 X2))) := by
    intro X1 X2
    first
    | (have i₁ := eq4282 X1 X2
       have i₂ := eq55 X1 X2
       grind)
    | exact superpose eq55 eq4282
    | exact resolve eq4282 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4282
  have eq4292 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 X2) (M.op X0 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4285 X0 X1 X2
       have i₂ := eq3502 X0 X1 (M.op X0 X2)
       grind)
    | exact superpose eq3502 eq4285
    | exact resolve eq4285 eq3502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3502 eq4285
  have eq4295 : ∀ X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (M.op X1 X2))) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq4289 X1 X2
       have i₂ := eq9 X2 X2 X1
       grind)
    | exact superpose eq9 eq4289
    | exact resolve eq4289 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4289
  have eq4297 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 (M.op X0 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4292 X0 X1 X2
       have i₂ := eq55 X0 X2
       grind)
    | exact superpose eq55 eq4292
    | exact resolve eq4292 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq4292
  have eq4356 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq301 (M.op X1 X1) X2 (M.op X0 (M.op X1 X0)) X3
       have i₂ := eq4295 X1 X0
       grind)
    | exact superpose eq4295 eq301
    | exact resolve eq301 eq4295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq4295
  have eq6159 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq117 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8605 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq62 x (M.op x x)
       have i₂ := eq4297 x x x
       grind)
    | exact superpose eq4297 eq62
    | exact resolve eq62 eq4297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq8637 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq8605 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq8605
    | exact resolve eq8605 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq8605
  have eq8680 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (M.op (σ X0) (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op (σ X0) (M.op (σ X0) (σ X0))) X0
       have i₂ := eq8637 (σ X0)
       grind)
    | exact superpose eq8637 eq28
    | exact resolve eq28 eq8637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq8687 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (k (τ (M.op (σ X0) (σ X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq8680 X0
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq8680
    | exact resolve eq8680 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq8680
  have eq21045 : ∀ X0 X1 X2 X3 : G, (σ X1) = (M.op (M.op X3 (σ X1)) (M.op (M.op (σ X0) (M.op X2 (σ X0))) (M.op (σ X1) (σ X0)))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4356 (σ X0) X2 (σ X1) X3
       have i₂ := eq871 X0 X1
       grind)
    | (have i₁ := eq4356 (σ X1) X1 (σ X0) X3
       have i₂ := eq871 X0 X1
       grind)
    | exact superpose eq871 eq4356
    | (have j1 := eq871 X0 X1
       grind)
    | exact resolve eq4356 eq871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871 eq4356
  have eq21098 : ∀ X0 X1 X3 : G, (σ X1) = (M.op (M.op X3 (σ X1)) (M.op (σ X0) (M.op (σ X1) (σ X0)))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq21045 X0 X1 x X3
       have i₂ := eq3106 (σ X1) (σ X0) x (σ X0)
       grind)
    | exact superpose eq3106 eq21045
    | (have j0 := eq21045 X0 X1 x X3
       grind)
    | exact resolve eq21045 eq3106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3106 eq21045
  have eq21147 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21098 X0 X1 x
       have i₂ := eq4297 (σ X1) x (σ X0)
       grind)
    | exact superpose eq4297 eq21098
    | (have j0 := eq21098 X0 X1 x
       grind)
    | exact resolve eq21098 eq4297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4297 eq21098
  have eq21168 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21147 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21147
    | exact resolve eq21147 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21176 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21147 y x
       grind)
    | exact superpose eq21147 eq16
    | (have j1 := eq21147 x y
       grind)
    | exact resolve eq16 eq21147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21147
  have eq21264 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21168 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq21168
    | (have j0 := eq21168 X0 X1
       grind)
    | exact resolve eq21168 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq21168
  have eq21271 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21264 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21264
    | exact resolve eq21264 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21264
  have eq21340 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq21176
       have i₂ := eq21271 x y
       grind)
    | exact superpose eq21271 eq21176
    | (have j1 := eq21271 (σ x) (σ y)
       grind)
    | (have r₁ := eq21176
       have r₂ := eq21271 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq21176
       have r₂ := eq21271 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq21176 eq21271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21176
  have eq21347 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq21340
  have eq21349 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq21347
       grind)
    | exact superpose eq21347 eq10
    | exact resolve eq10 eq21347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21347
  have eq21392 : x = y ∨ x = y := by
    first
    | (have i₁ := eq21349
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq21349
    | exact resolve eq21349 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21349
  have eq21393 : x = y := by grind
  clear eq21392
  have eq21394 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21393
       grind)
    | exact superpose eq21393 eq16
    | exact resolve eq16 eq21393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21393
  have eq21395 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21394
       have i₂ := eq117 x
       grind)
    | exact superpose eq117 eq21394
    | (have j1 := eq117 x
       grind)
    | exact resolve eq21394 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq103162 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21395
       have i₂ := eq96 x
       grind)
    | exact superpose eq96 eq21395
    | (have j1 := eq96 (σ x)
       grind)
    | exact resolve eq21395 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21395
  have eq103163 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq103162
  have eq103179 : (τ (σ x)) = (k x (k (τ (σ x)) x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq8687 x
       have i₂ := eq103163
       grind)
    | exact superpose eq103163 eq8687
    | exact resolve eq8687 eq103163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8687 eq103163
  have eq103348 : x = (k x (k x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq103179
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq103179
    | exact resolve eq103179 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103179
  have eq103353 : x = (k x (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq103348
       have i₂ := eq96 x
       grind)
    | exact superpose eq96 eq103348
    | (have j1 := eq96 x
       grind)
    | exact resolve eq103348 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq103348
  have eq103376 : x = (k x (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq103353
  have eq103381 : x = (M.op (M.op x x) x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21271 (M.op x x) x
       have i₂ := eq103376
       grind)
    | exact superpose eq103376 eq21271
    | (have j0 := eq21271 x (M.op (M.op x x) x)
       grind)
    | exact resolve eq21271 eq103376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21271 eq103376
  have eq103415 : x = (M.op (M.op x x) x) ∨ x = (M.op x x) := by grind
  clear eq103381
  have eq103434 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq103415
       have i₂ := eq316 x x
       grind)
    | exact superpose eq316 eq103415
    | exact resolve eq103415 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316 eq103415
  have eq103435 : x = (M.op x x) := by grind
  clear eq103434
  have eq103468 : x = (k x (M.op x x)) := by
    first
    | (have i₁ := eq8637 x
       have i₂ := eq103435
       grind)
    | exact superpose eq103435 eq8637
    | exact resolve eq8637 eq103435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8637
  have eq103592 : x = (k x x) := by
    first
    | (have i₁ := eq103468
       have i₂ := eq103435
       grind)
    | exact superpose eq103435 eq103468
    | exact resolve eq103468 eq103435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103468
  have eq103815 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6159 x
       have i₂ := eq103592
       grind)
    | exact superpose eq103592 eq6159
    | (have j0 := eq6159 x
       grind)
    | exact resolve eq6159 eq103592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6159 eq103592
  have eq103818 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq103815
  have eq103830 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq21394
       have i₂ := eq103818
       grind)
    | exact superpose eq103818 eq21394
    | exact resolve eq21394 eq103818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21394 eq103818
  have eq104023 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq103830
       have i₂ := eq103435
       grind)
    | exact superpose eq103435 eq103830
    | exact resolve eq103830 eq103435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103435 eq103830
  have eq104024 : False := by grind
  exact eq104024

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_y_pyy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
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
  have eq47 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
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
  have eq50 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq85 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq86 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq85
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq85
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq85
       grind)
    | exact superpose eq85 eq16
    | exact resolve eq16 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq90
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq90
    | exact resolve eq90 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq97
    | exact resolve eq97 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq99 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq86
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq86 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq16
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq99
  have eq114 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq155 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq114 eq16
    | exact resolve eq16 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq165 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq104
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq104 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq167 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq165
  have eq204 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq155
       have i₂ := eq11 sF1 sF1
       grind)
    | exact superpose eq11 eq155
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq155 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq206 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq204
  have eq207 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq47 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq47 eq14
    | exact resolve eq14 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq207 eq47
    | exact resolve eq47 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : (M.op x y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq207 eq48
    | exact resolve eq48 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq48 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq48 eq14
    | exact resolve eq14 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq47 eq50
    | exact resolve eq50 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq50 X0 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (M.op X1 X0)
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq48
    | exact resolve eq48 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (M.op X1 X0)
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq47
    | exact resolve eq47 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X0 (M.op X1 X0)) (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq379 : (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq207 eq371
    | exact resolve eq371 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq49 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3 X4
       have i₂ := eq49 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq49 eq49
    | exact resolve eq49 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 X4 X2 X3 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq49 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq49 eq49
    | exact resolve eq49 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq422 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq49 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq49 eq14
    | exact resolve eq14 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    grind
  have eq424 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq49 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq49 eq47
    | exact resolve eq47 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq50 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq49 X0 x x X3
       grind)
    | exact superpose eq49 eq50
    | exact resolve eq50 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq433 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq424 X0 X1
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq424
    | exact resolve eq424 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq434 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq423 X0 X1
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq423
    | exact resolve eq423 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq435 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq422 X0 X1 X2 X3
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq422
    | exact resolve eq422 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq440 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq413 X0 X1 X2 X3 X4
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq413
    | exact resolve eq413 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq441 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq406 X0 X1 X2 X3 X4
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq406
    | exact resolve eq406 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq632 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq63 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq63 X0 X0
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq634 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq63 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq637 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq632 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq645 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq637 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq637 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq637 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq637 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq655 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq645 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq645
    | (have j0 := eq645 X0 X1
       grind)
    | exact resolve eq645 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq1090 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq209 eq47
    | exact resolve eq47 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1114 : (M.op (M.op x y) (M.op y (M.op x y))) = (M.op y (M.op y (M.op x y))) := by
    first
    | exact superpose eq207 eq1090
    | exact resolve eq1090 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1189 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq218 eq47
    | exact resolve eq47 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1190 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq218 eq48
    | exact resolve eq48 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1216 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq216 eq1190
    | exact resolve eq1190 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190
  have eq1217 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq216 eq1189
    | exact resolve eq1189 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189
  have eq1420 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq373 (M.op X0 X0) (M.op X1 (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq373
    | exact resolve eq373 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1426 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) = (M.op y (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq373 (M.op x sF0) (M.op x sF0)
       have i₂ := eq14 (M.op x sF0) sF0 x
       grind)
    | exact superpose eq14 eq373
    | exact resolve eq373 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1436 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op x y))) = (M.op y (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1426 X0
       have i₂ := eq50 X0 sF0
       grind)
    | exact superpose eq50 eq1426
    | exact resolve eq1426 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426
  have eq1472 : (M.op x y) = (M.op (M.op x y) (M.op y (M.op y (M.op x y)))) := by
    first
    | exact superpose eq1114 eq379
    | exact resolve eq379 eq1114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq1586 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq393 X1 (M.op X0 (M.op X0 X0)) X2
       have i₂ := eq393 X0 X0 X0
       grind)
    | exact superpose eq393 eq393
    | exact resolve eq393 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1588 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq209 eq393
    | exact resolve eq393 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq1589 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq218 eq393
    | exact resolve eq393 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq1591 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y (M.op x y))) (M.op (M.op x y) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq207 eq393
    | exact resolve eq393 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1605 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq393 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq393 X0 X0 X0
       grind)
    | exact superpose eq393 eq393
    | exact resolve eq393 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1610 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 (M.op X1 X1)) (M.op X1 (M.op y (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq207 eq393
    | exact resolve eq393 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1634 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq393 X0 X0 X0
       grind)
    | exact superpose eq393 eq14
    | exact resolve eq14 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1636 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (M.op X0 (M.op X0 X0))
       have i₂ := eq393 X0 X0 X0
       grind)
    | exact superpose eq393 eq47
    | exact resolve eq47 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq1637 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (M.op X0 (M.op X0 X0))
       have i₂ := eq393 X0 X0 X0
       grind)
    | exact superpose eq393 eq48
    | exact resolve eq48 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1644 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq366 (M.op x (M.op x x))
       have i₂ := eq393 x x x
       grind)
    | exact superpose eq393 eq366
    | exact resolve eq366 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq1647 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq427 (M.op x (M.op x x)) x
       have i₂ := eq393 x x x
       grind)
    | exact superpose eq393 eq427
    | exact resolve eq427 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1683 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq216 eq1589
    | exact resolve eq1589 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1589
  have eq1684 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op (M.op x y) (M.op y (M.op x y))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq207 eq1588
    | exact resolve eq1588 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1588
  have eq1698 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op y (M.op y (M.op x y))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1114 eq1684
    | exact resolve eq1684 eq1114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114 eq1684
  have eq1776 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1216 eq1217
    | exact resolve eq1217 eq1216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217
  have eq1878 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq371 X0
       have i₂ := eq1636 X0
       grind)
    | exact superpose eq1636 eq371
    | exact resolve eq371 eq1636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1880 : ∀ X0 X1 : G, (M.op (M.op y (M.op (M.op x y) X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq393 X0 X0 X1
       have i₂ := eq1636 X0
       grind)
    | exact superpose eq1636 eq393
    | exact resolve eq393 eq1636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1883 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op y (M.op (M.op x y) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq427 X0 X0
       have i₂ := eq1636 X0
       grind)
    | exact superpose eq1636 eq427
    | exact resolve eq427 eq1636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1907 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1636 eq372
    | exact resolve eq372 eq1636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1919 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq372 eq1907
    | exact resolve eq1907 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1907
  have eq1957 : (M.op y (M.op x y)) = (M.op (M.op y (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq210 eq1878
    | exact resolve eq1878 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq1878
  have eq2123 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1637 eq372
    | exact resolve eq372 eq1637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1637
  have eq2135 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq372 eq2123
    | exact resolve eq2123 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq2123
  have eq2253 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1644 (M.op (M.op x sF0) (M.op X0 X0))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq1644
    | exact resolve eq1644 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1644
  have eq2300 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2253 X0 X1
       have i₂ := eq1636 (M.op (M.op X1 sF0) (M.op X0 X0))
       grind)
    | exact superpose eq1636 eq2253
    | exact resolve eq2253 eq1636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2253
  have eq2316 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2300 X0 x
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq2300
    | exact resolve eq2300 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2300
  have eq2511 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1647 X0 X1
       have i₂ := eq1636 X0
       grind)
    | exact superpose eq1636 eq1647
    | exact resolve eq1647 eq1636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4437 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)))) = (M.op (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq433 (M.op X1 (M.op X0 X0)) (M.op X0 X0)
       have i₂ := eq14 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq433
    | exact resolve eq433 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4471 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op y (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq374 X1 X0 X1 X0
       have i₂ := eq433 X0 X1
       grind)
    | exact superpose eq433 eq374
    | exact resolve eq374 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq4523 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4437 X0 X1
       have i₂ := eq427 X0 (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq427 eq4437
    | exact resolve eq4437 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4437
  have eq5684 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq435 X0 X1 X2 X3
       have i₂ := eq433 X0 X1
       grind)
    | exact superpose eq433 eq435
    | exact resolve eq435 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq5838 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X1 (M.op X0 X0)))) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5684 X1 (M.op X0 X0) (M.op X1 X1) x
       have i₂ := eq393 x X1 X0
       grind)
    | exact superpose eq393 eq5684
    | exact resolve eq5684 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5847 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op X2 (M.op X1 (M.op X0 X1))))) = (M.op (M.op X2 X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5684 X2 (M.op X1 (M.op X0 X1)) (M.op X2 X2) (M.op x x)
       have i₂ := eq412 X1 X0 x x X2
       grind)
    | exact superpose eq412 eq5684
    | exact resolve eq5684 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5862 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op X2 X1)) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5684 (M.op X3 (M.op X2 X1)) (M.op X0 X0) X1 X2
       have i₂ := eq14 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq14 eq5684
    | exact resolve eq5684 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5892 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op (M.op X2 (M.op X0 X1)) (M.op X0 X1)))) = (M.op (M.op (M.op X2 (M.op X0 X1)) (M.op X0 X1)) (M.op y (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq433 (M.op X2 (M.op X0 X1)) (M.op X0 X1)
       have i₂ := eq5684 X0 X1 (M.op X0 X1) X2
       grind)
    | exact superpose eq5684 eq433
    | exact resolve eq433 eq5684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5684
  have eq5953 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op y (M.op (M.op x y) (M.op (M.op X2 (M.op X0 X1)) (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2511 eq5892
    | exact resolve eq5892 eq2511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2511 eq5892
  have eq8458 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (k (M.op X0 X1) (M.op y (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq434 X0 X1
       have i₂ := eq433 X0 X1
       grind)
    | exact superpose eq433 eq434
    | exact resolve eq434 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq8729 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq440 X0 X1 X2 X3 X4
       have i₂ := eq433 X0 X1
       grind)
    | exact superpose eq433 eq440
    | exact resolve eq440 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq8842 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) X0)) = (M.op (M.op (M.op X1 X2) (M.op X3 X3)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8729 X0 (M.op X0 (M.op X0 X0)) X2 X3 x
       have i₂ := eq371 X0
       grind)
    | exact superpose eq371 eq8729
    | exact resolve eq8729 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8729
  have eq9257 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) (M.op (M.op y (M.op (M.op x y) (M.op X0 X1))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq441 X0 X1 X2 X3 X4
       have i₂ := eq433 X0 X1
       grind)
    | exact superpose eq433 eq441
    | exact resolve eq441 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433 eq441
  have eq9473 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) (M.op (M.op y (M.op x y)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9257 sF0 (M.op sF0 sF0) X2 x x
       have i₂ := eq371 sF0
       grind)
    | exact superpose eq371 eq9257
    | exact resolve eq9257 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9257
  have eq9635 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op y (M.op (M.op x y) (M.op x y)))) (M.op (M.op y (M.op x y)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq1436 eq9473
    | exact resolve eq9473 eq1436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436 eq9473
  have eq9705 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op y (M.op y (M.op x y)))) (M.op (M.op y (M.op x y)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq207 eq9635
    | exact resolve eq9635 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9635
  have eq12005 : ∀ X0 X1 : G, (σ (M.op y (M.op (M.op x y) (M.op X0 X1)))) ≠ (σ (M.op y (M.op (M.op x y) (M.op X0 X1)))) ∨ (σ (M.op y (M.op (M.op x y) (M.op X0 X1)))) = (M.op (σ (M.op y (M.op (M.op x y) (M.op X0 X1)))) (σ (M.op y (M.op (M.op x y) (M.op X0 X1))))) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op y (M.op (M.op x y) (M.op X0 X1)))) (σ (M.op y (M.op (M.op x y) (M.op X0 X1))))) := by
    intro X0 X1
    first
    | exact superpose eq8458 eq655
    | (have j0 := eq655 (M.op y (M.op (M.op x y) (M.op X0 X1))) (M.op y (M.op (M.op x y) (M.op X0 X1)))
       grind)
    | exact resolve eq655 eq8458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8458
  have eq12120 : ∀ X0 X1 : G, (σ (M.op y (M.op (M.op x y) (M.op X0 X1)))) = (M.op (σ (M.op y (M.op (M.op x y) (M.op X0 X1)))) (σ (M.op y (M.op (M.op x y) (M.op X0 X1))))) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op y (M.op (M.op x y) (M.op X0 X1)))) (σ (M.op y (M.op (M.op x y) (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have j0 := eq12005 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12005
  have eq17557 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq17558 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq17557
    | exact resolve eq17557 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17557
  have eq17569 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq17558
       have r₂ := eq28
       grind)
    | exact resolve eq17558 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17558
  have eq17571 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq17569
    | exact resolve eq17569 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17569
  have eq17574 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq17571
  have eq17670 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17574 eq95
    | exact resolve eq95 eq17574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq17574
  have eq17695 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq29 eq17670
    | exact resolve eq17670 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17670
  have eq20120 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y x) := by grind
  clear eq17695
  have eq20185 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20120
  have eq20234 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq634 x y
       have i₂ := eq20185
       grind)
    | exact superpose eq20185 eq634
    | (have j0 := eq634 x y
       grind)
    | exact resolve eq634 eq20185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq20235 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq20185
       grind)
    | exact superpose eq20185 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq20185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20185
  have eq20236 : x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20235
  have eq20237 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20234
  have eq20240 : x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20236
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20236
    | exact resolve eq20236 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20236
  have eq20241 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20240
  have eq20242 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20237
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20237
    | exact resolve eq20237 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20237
  have eq20255 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20242
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20242
    | exact resolve eq20242 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20242
  have eq20259 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq20255
    | exact resolve eq20255 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20255
  have eq20260 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq20259
  have eq20264 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20260
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20260
    | exact resolve eq20260 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20260
  have eq20267 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20264
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20264
    | exact resolve eq20264 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20264
  have eq20320 : y = (k (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq375 x x
       have i₂ := eq20241
       grind)
    | exact superpose eq20241 eq375
    | exact resolve eq375 eq20241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375 eq20241
  have eq20352 : y = (k (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20320
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20320
    | exact resolve eq20320 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20320
  have eq20428 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20267 eq371
    | exact resolve eq371 eq20267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20453 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20267 eq50
    | exact resolve eq50 eq20267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20267
  have eq20492 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq20453
    | exact resolve eq20453 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20453
  have eq20500 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq20428
    | exact resolve eq20428 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20428
  have eq20640 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20352 eq655
    | (have j0 := eq655 y y
       grind)
    | exact resolve eq655 eq20352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655 eq20352
  have eq20645 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20640
  have eq20648 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20645
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20645
    | exact resolve eq20645 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20645
  have eq20659 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20648
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20648
    | exact resolve eq20648 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20648
  have eq20663 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq20659
    | exact resolve eq20659 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20659
  have eq27403 : ∀ X0 : G, (M.op x y) = (M.op (M.op y (M.op (M.op x y) X0)) (M.op X0 (M.op y (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq1610 X0 X0
       have i₂ := eq1636 X0
       grind)
    | exact superpose eq1636 eq1610
    | exact resolve eq1610 eq1636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1610
  have eq28379 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq412 X0 (M.op X1 X0) X2 X3 X4
       have i₂ := eq1634 X0 X0 X1
       grind)
    | exact superpose eq1634 eq412
    | exact resolve eq412 eq1634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1634
  have eq28452 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq28379 X0 X1 x x x
       have i₂ := eq412 X0 X0 x x x
       grind)
    | exact superpose eq412 eq28379
    | exact resolve eq28379 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq28379
  have eq43448 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1216 eq1683
    | exact resolve eq1683 eq1216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216 eq1683
  have eq43449 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1776 eq43448
    | exact resolve eq43448 eq1776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776 eq43448
  have eq69945 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) X0)))) := by
    intro X0
    first
    | (have i₁ := eq4523 X0 x
       have i₂ := eq1420 X0 x
       grind)
    | exact superpose eq1420 eq4523
    | exact resolve eq4523 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420 eq4523
  have eq85916 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op y (M.op (M.op x y) X0))) (M.op X2 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5862 X2 (M.op X1 X0) (M.op (M.op x x) (M.op X1 X1)) X3
       have i₂ := eq8842 X0 x x X1
       grind)
    | exact superpose eq8842 eq5862
    | exact resolve eq5862 eq8842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8842
  have eq85933 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op x y) X0) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq5862 eq85916
    | exact resolve eq85916 eq5862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85916
  have eq143475 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20492 eq20663
    | exact resolve eq20663 eq20492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20492 eq20663
  have eq143688 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq143475
  have eq143729 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq143688
       have r₂ := eq28
       grind)
    | exact resolve eq143688 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143688
  have eq143803 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq143729 eq20500
    | exact resolve eq20500 eq143729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20500
  have eq143928 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq143729
  have eq144050 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq143803
  have eq144099 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq144050
    | exact resolve eq144050 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144050
  have eq144100 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq144099
  have eq144109 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq144100
       have r₂ := eq143928
       grind)
    | exact resolve eq144100 eq143928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143928 eq144100
  have eq144111 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq144109 eq28
    | exact resolve eq28 eq144109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144112 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq144109 eq48
    | exact resolve eq48 eq144109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq144114 : (M.op x y) = (M.op (σ y) (M.op (σ x) (M.op y (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq144109 eq215
    | exact resolve eq215 eq144109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq144152 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq144109 eq2135
    | exact resolve eq2135 eq144109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2135
  have eq144165 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq144152
    | exact resolve eq144152 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144152
  have eq144205 : (σ y) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by grind
  have eq144285 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq144165 eq43449
    | exact resolve eq43449 eq144165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43449
  have eq144400 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1883 eq144285
    | exact resolve eq144285 eq1883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883 eq144285
  have eq144429 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq216 eq144400
    | exact resolve eq144400 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq144400
  have eq144445 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq144109 eq144205
    | exact resolve eq144205 eq144109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144458 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq144445
  have eq144464 : (τ (σ y)) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq144458 eq58
    | exact resolve eq58 eq144458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq144458
  have eq144509 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq144464
    | exact resolve eq144464 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144464
  have eq144532 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq144509
       grind)
    | exact superpose eq144509 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq144509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144509
  have eq144533 : y = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq144532
  have eq148535 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq144165 eq144112
    | exact resolve eq144112 eq144165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148617 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op (M.op X1 X0) X0))) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq144112 eq5953
    | exact resolve eq5953 eq144112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5953 eq144112
  have eq148641 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by grind
  clear eq148535
  have eq148835 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq144109 eq148641
    | exact resolve eq148641 eq144109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144109 eq148641
  have eq148932 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq148835
  have eq148981 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq148932 eq393
    | exact resolve eq393 eq148932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148932
  have eq149103 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq148981 x
       have i₂ := eq427 sF3 x
       grind)
    | exact superpose eq427 eq148981
    | exact resolve eq148981 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427 eq148981
  have eq149980 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) (M.op X0 X0)))) = (M.op (M.op (σ x) (M.op y (M.op x y))) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq144114 eq5862
    | exact resolve eq5862 eq144114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144114
  have eq150007 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (σ x) (M.op y (M.op x y))) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq149980 X0 x
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq149980
    | exact resolve eq149980 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149980
  have eq213187 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5847 (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)) (M.op X1 X0)
       have i₂ := eq1586 X0 X1 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq1586 eq5847
    | exact resolve eq5847 eq1586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1586 eq5847
  have eq214641 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq213187 X0 X1
       have i₂ := eq50 X0 (M.op X0 X0)
       grind)
    | exact superpose eq50 eq213187
    | exact resolve eq213187 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213187
  have eq214773 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq214641 X0 X1
       have i₂ := eq1647 X0 X0
       grind)
    | exact superpose eq1647 eq214641
    | exact resolve eq214641 eq1647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647 eq214641
  have eq214816 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq214773 X0 X1
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq214773
    | exact resolve eq214773 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq214773
  have eq214827 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | exact superpose eq373 eq214816
    | exact resolve eq214816 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373 eq214816
  have eq272307 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq148617 eq4471
    | exact resolve eq4471 eq148617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4471 eq148617
  have eq285066 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op y (M.op (M.op x y) (M.op y (M.op X0 X0)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq150007 eq5862
    | exact resolve eq5862 eq150007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5862 eq150007
  have eq285859 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op y y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5838 eq285066
    | exact resolve eq285066 eq5838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5838 eq285066
  have eq286178 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op x y)) (M.op (M.op y (M.op y (M.op x y))) (M.op (M.op x y) (M.op y y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1698 X0 (M.op y y)
       have i₂ := eq285859 (M.op y y)
       grind)
    | exact superpose eq285859 eq1698
    | exact resolve eq1698 eq285859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1698 eq285859
  have eq286819 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op x y)) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1591 eq286178
    | exact resolve eq286178 eq1591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1591 eq286178
  have eq1970572 : ∀ X0 X1 : G, (σ (M.op y (M.op (M.op x y) (M.op X0 X1)))) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (σ (M.op y (M.op (M.op x y) (M.op X0 X1)))))))) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op y (M.op (M.op x y) (M.op X0 X1)))) (σ (M.op y (M.op (M.op x y) (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq12120 X0 X1
       have i₂ := eq69945 (σ (M.op y (M.op sF0 (M.op X0 X1))))
       grind)
    | exact superpose eq69945 eq12120
    | (have j0 := eq12120 X0 X1
       grind)
    | exact resolve eq12120 eq69945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12120
  have eq1970573 : ∀ X0 X1 : G, (σ (M.op y (M.op (M.op x y) (M.op X0 X1)))) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (σ (M.op y (M.op (M.op x y) (M.op X0 X1)))))))) ∨ (σ (M.op X0 X1)) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (σ (M.op y (M.op (M.op x y) (M.op X0 X1)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1970572 X0 X1
       have i₂ := eq69945 (σ (M.op y (M.op sF0 (M.op X0 X1))))
       grind)
    | exact superpose eq69945 eq1970572
    | (have j0 := eq1970572 X0 X1
       grind)
    | exact resolve eq1970572 eq69945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1970572
  have eq3284179 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq149103 eq167
    | exact resolve eq167 eq149103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149103
  have eq3284180 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq144165 eq167
    | exact resolve eq167 eq144165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq3284785 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq3284179
    | exact resolve eq3284179 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3284179
  have eq3284807 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq3284785
       grind)
    | exact superpose eq3284785 eq86
    | exact resolve eq86 eq3284785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3284785
  have eq3285300 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3284807
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3284807
    | exact resolve eq3284807 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3284807
  have eq3286184 : (k (σ y) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq3284180
       grind)
    | exact superpose eq3284180 eq86
    | exact resolve eq86 eq3284180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq3284180
  have eq3286692 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3286184
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq3286184
    | exact resolve eq3286184 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3286184
  have eq3348446 : ∀ X0 : G, (M.op (σ y) (M.op y (σ y))) = (M.op (M.op X0 (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq144165 eq2316
    | exact resolve eq2316 eq144165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144165
  have eq3352339 : (σ y) = (M.op (M.op (σ y) (M.op y (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3348446 eq144429
    | exact resolve eq144429 eq3348446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144429 eq3348446
  have eq3353043 : (σ y) = (M.op (M.op (σ y) (M.op y (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by grind
  clear eq3352339
  have eq3353520 : (σ y) = (M.op (M.op (M.op x y) (M.op y (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3353043
       have i₂ := eq85933 (M.op y sF3) sF3 (M.op sF3 sF4)
       grind)
    | exact superpose eq85933 eq3353043
    | exact resolve eq3353043 eq85933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3353043
  have eq3355808 : ∀ X0 : G, (M.op (M.op (σ y) (M.op y (M.op y (M.op x y)))) (M.op (M.op y (M.op x y)) (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3353520 eq9705
    | exact resolve eq9705 eq3353520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9705 eq3353520
  have eq3356254 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op y (M.op y (M.op x y)))) (M.op (M.op y (M.op x y)) (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3355808 X0
       have i₂ := eq85933 (M.op y (M.op y sF0)) sF3 (M.op (M.op y sF0) (M.op X0 X0))
       grind)
    | exact superpose eq85933 eq3355808
    | exact resolve eq3355808 eq85933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85933 eq3355808
  have eq3356509 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op y (M.op y (M.op x y)))) (M.op X0 (M.op y X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2316 eq3356254
    | exact resolve eq3356254 eq2316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2316 eq3356254
  have eq3356629 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1472 eq3356509
    | exact resolve eq3356509 eq1472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472 eq3356509
  have eq3358305 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3356629 x
       have i₂ := eq144533
       grind)
    | exact superpose eq144533 eq3356629
    | exact resolve eq3356629 eq144533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144533 eq3356629
  have eq3359312 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq3358305
  have eq3359704 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3359312
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3359312
    | exact resolve eq3359312 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3359312
  have eq3359910 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq207 eq3359704
    | exact resolve eq3359704 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3359704
  have eq3370743 : x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq3359910 eq1957
    | exact resolve eq1957 eq3359910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957 eq3359910
  have eq3373011 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq272307 y y
       have i₂ := eq3370743
       grind)
    | exact superpose eq3370743 eq272307
    | exact resolve eq272307 eq3370743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272307 eq3370743
  have eq3373118 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by grind
  clear eq3373011
  have eq3373250 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq3373118
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3373118
    | exact resolve eq3373118 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3373118
  have eq3373251 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq3373250
  have eq3373822 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3373251 eq286819
    | exact resolve eq286819 eq3373251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286819
  have eq3374290 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq3373822
  have eq3374530 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3374290
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3374290
    | exact resolve eq3374290 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3374290
  have eq3375175 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq3374530
       grind)
    | exact superpose eq3374530 eq105
    | exact resolve eq105 eq3374530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3374530
  have eq3376386 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq3375175
    | exact resolve eq3375175 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3375175
  have eq3417330 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3376386 eq3285300
    | exact resolve eq3285300 eq3376386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3285300
  have eq3417331 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3376386 eq3286692
    | exact resolve eq3286692 eq3376386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3286692
  have eq3417562 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq3417331
  have eq3417563 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq3417330
  have eq3417620 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq3417562
       have r₂ := eq28
       grind)
    | exact resolve eq3417562 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3417562
  have eq3417621 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq3417563
       have r₂ := eq144111
       grind)
    | exact resolve eq3417563 eq144111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144111 eq3417563
  have eq3417672 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3417620 eq28
    | exact resolve eq28 eq3417620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3417893 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3417620 eq144205
    | exact resolve eq144205 eq3417620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144205 eq3417620
  have eq3419802 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq3417893
  have eq3420624 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3417621 eq30
    | exact resolve eq30 eq3417621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3417621
  have eq3423713 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq3420624
    | exact resolve eq3420624 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3420624
  have eq3425194 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq3423713 eq3373251
    | exact resolve eq3373251 eq3423713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3373251 eq3423713
  have eq3425242 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq3425194
  have eq3426079 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3425242
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3425242
    | exact resolve eq3425242 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3425242
  have eq3426080 : x = (M.op x y) ∨ x = y := by grind
  clear eq3426079
  have eq3426425 : (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq3426080 eq207
    | exact resolve eq207 eq3426080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3426493 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq3426080 eq1919
    | exact resolve eq1919 eq3426080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3427051 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq3426493
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3426493
    | exact resolve eq3426493 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3426493
  have eq3428834 : y = (M.op y (M.op y (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq371 y
       have i₂ := eq3427051
       grind)
    | exact superpose eq3427051 eq371
    | exact resolve eq371 eq3427051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq3427051
  have eq3442828 : y = (M.op y (M.op y x)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq3426080 eq3428834
    | exact resolve eq3428834 eq3426080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3428834
  have eq3443316 : y = (M.op y (M.op y x)) ∨ x = y := by grind
  clear eq3442828
  have eq3450807 : y = (M.op y (M.op x x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq3443316
       have i₂ := eq3426425
       grind)
    | exact superpose eq3426425 eq3443316
    | exact resolve eq3443316 eq3426425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3426425 eq3443316
  have eq3451256 : y = (M.op y (M.op x x)) ∨ x = y := by grind
  clear eq3450807
  have eq3452865 : x = (M.op (M.op y (M.op (M.op x y) y)) y) ∨ x = y := by
    first
    | (have i₁ := eq1880 y x
       have i₂ := eq3451256
       grind)
    | exact superpose eq3451256 eq1880
    | exact resolve eq1880 eq3451256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1880 eq3451256
  have eq3453536 : x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq3452865
       have i₂ := eq214827 y sF0
       grind)
    | exact superpose eq214827 eq3452865
    | exact resolve eq3452865 eq214827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214827 eq3452865
  have eq3453713 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq105
       have i₂ := eq3453536
       grind)
    | exact superpose eq3453536 eq105
    | exact resolve eq105 eq3453536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq3453536
  have eq3454512 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by grind
  clear eq3453713
  have eq3454869 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq3454512
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3454512
    | exact resolve eq3454512 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3454512
  have eq3466378 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3419802 eq3376386
    | exact resolve eq3376386 eq3419802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3376386 eq3419802
  have eq3466615 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq3466378
  have eq3466685 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3466615
       have r₂ := eq3417672
       grind)
    | exact resolve eq3466615 eq3417672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3417672 eq3466615
  have eq3468114 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq3466685
  have eq3468119 : x = (M.op x y) := by
    first
    | (have r₁ := eq3468114
       have r₂ := eq3426080
       grind)
    | exact resolve eq3468114 eq3426080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3426080 eq3468114
  have eq3468345 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq3468119 eq21
    | exact resolve eq21 eq3468119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq3468394 : (M.op x x) = (M.op y x) := by
    first
    | exact superpose eq3468119 eq207
    | exact resolve eq207 eq3468119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq3468462 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq3468119 eq1919
    | exact resolve eq1919 eq3468119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1919
  have eq3469031 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq3468462
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3468462
    | exact resolve eq3468462 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3468462
  have eq3469102 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3468345
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3468345
    | exact resolve eq3468345 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3468345
  have eq3469178 : x = (M.op y y) := by
    first
    | exact superpose eq3468119 eq3469031
    | exact resolve eq3469031 eq3468119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3469031
  have eq3469211 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq3469102 eq27
    | exact resolve eq27 eq3469102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq3470917 : y = (k x y) := by grind
  have eq3470931 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op X1 X1)) (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq393 X0 X1 y
       have i₂ := eq3469178
       grind)
    | exact superpose eq3469178 eq393
    | exact resolve eq393 eq3469178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393 eq3469178
  have eq3472138 : y = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq3470931 x x
       have i₂ := eq1605 x x x
       grind)
    | exact superpose eq1605 eq3470931
    | exact resolve eq3470931 eq1605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1605 eq3470931
  have eq3478388 : ∀ X0 : G, x = (M.op (M.op y (M.op x X0)) (M.op X0 (M.op y x))) := by
    intro X0
    first
    | exact superpose eq3468119 eq27403
    | exact resolve eq27403 eq3468119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27403
  have eq3478389 : ∀ X0 : G, x = (M.op (M.op y (M.op x X0)) (M.op X0 (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq3478388 X0
       have i₂ := eq3468394
       grind)
    | exact superpose eq3468394 eq3478388
    | exact resolve eq3478388 eq3468394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3468394 eq3478388
  have eq3479270 : (σ (M.op y (M.op (M.op x y) x))) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (σ (M.op y (M.op (M.op x y) x))))))) ∨ (σ x) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (σ (M.op y (M.op (M.op x y) x))))))) := by
    first
    | (have i₁ := eq1970573 (M.op y (M.op x x)) (M.op x (M.op x x))
       have i₂ := eq3478389 x
       grind)
    | exact superpose eq3478389 eq1970573
    | exact resolve eq1970573 eq3478389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1970573 eq3478389
  have eq3479313 : (σ (M.op y (M.op (M.op x y) x))) = (M.op (σ (M.op y (M.op (M.op x y) x))) (σ (M.op y (M.op (M.op x y) x)))) ∨ (σ x) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (σ (M.op y (M.op (M.op x y) x))))))) := by
    first
    | exact superpose eq69945 eq3479270
    | exact resolve eq3479270 eq69945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3479270
  have eq3479804 : (σ (M.op x (M.op x x))) = (M.op (σ (M.op x (M.op x x))) (σ (M.op x (M.op x x)))) ∨ (σ x) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (σ (M.op y (M.op (M.op x y) x))))))) := by
    first
    | exact superpose eq1636 eq3479313
    | exact resolve eq3479313 eq1636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3479313
  have eq3480121 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (σ (M.op y (M.op (M.op x y) x))))))) := by
    first
    | (have i₁ := eq3479804
       have i₂ := eq3472138
       grind)
    | exact superpose eq3472138 eq3479804
    | exact resolve eq3479804 eq3472138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3479804
  have eq3480305 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (σ (M.op y (M.op (M.op x y) x))))))) := by
    first
    | (have i₁ := eq3480121
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3480121
    | exact resolve eq3480121 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3480121
  have eq3480417 : (σ x) = (M.op (σ (M.op y (M.op (M.op x y) x))) (σ (M.op y (M.op (M.op x y) x)))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq69945 eq3480305
    | exact resolve eq3480305 eq69945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69945 eq3480305
  have eq3480467 : (σ x) = (M.op (σ (M.op x (M.op x x))) (σ (M.op x (M.op x x)))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1636 eq3480417
    | exact resolve eq3480417 eq1636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1636 eq3480417
  have eq3480488 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3480467
       have i₂ := eq3472138
       grind)
    | exact superpose eq3472138 eq3480467
    | exact resolve eq3480467 eq3472138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3472138 eq3480467
  have eq3480498 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3480488
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3480488
    | exact resolve eq3480488 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3480488
  have eq3480506 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3480498
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3480498
    | exact resolve eq3480498 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3480498
  have eq3480513 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3469102 eq3480506
    | exact resolve eq3480506 eq3469102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3480506
  have eq3521024 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  have eq3521741 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq3480513
  have eq3524210 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3521024 eq3454869
    | exact resolve eq3454869 eq3521024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3454869 eq3521024
  have eq3524546 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3469102 eq3524210
    | exact resolve eq3524210 eq3469102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3524210
  have eq3524609 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq3524546
       have r₂ := eq3521741
       grind)
    | exact resolve eq3524546 eq3521741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3521741 eq3524546
  have eq3525568 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3524609 eq28452
    | exact resolve eq28452 eq3524609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28452 eq3524609
  have eq3525767 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3469211 eq3525568
    | exact resolve eq3525568 eq3469211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3525568
  have eq3526302 : x = y := by
    first
    | (have r₁ := eq3525767
       have r₂ := eq28
       grind)
    | exact resolve eq3525767 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3525767
  have eq3526924 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq3526302
       grind)
    | exact superpose eq3526302 eq25
    | exact resolve eq25 eq3526302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq3527914 : x = (k x x) := by
    first
    | (have i₁ := eq3470917
       have i₂ := eq3526302
       grind)
    | exact superpose eq3526302 eq3470917
    | exact resolve eq3470917 eq3526302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3470917 eq3526302
  have eq3528346 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3526924
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3526924
    | exact resolve eq3526924 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3526924
  have eq3528607 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3469102 eq3528346
    | exact resolve eq3528346 eq3469102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3528346
  have eq3530265 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3528607 eq3469211
    | exact resolve eq3469211 eq3528607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3469211 eq3528607
  have eq3539396 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3530265 eq206
    | exact resolve eq206 eq3530265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq3530265
  have eq3540705 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq3539396
       have r₂ := eq28
       grind)
    | exact resolve eq3539396 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3539396
  have eq3541215 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3468119 eq3540705
    | exact resolve eq3540705 eq3468119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3468119 eq3540705
  have eq3541526 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3541215
       have i₂ := eq3527914
       grind)
    | exact superpose eq3527914 eq3541215
    | exact resolve eq3541215 eq3527914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3527914 eq3541215
  have eq3542111 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3541526 eq15
    | exact resolve eq15 eq3541526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3541526
  have eq3543090 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3542111
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3542111
    | exact resolve eq3542111 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3542111
  have eq3543357 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3469102 eq3543090
    | exact resolve eq3543090 eq3469102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3469102 eq3543090
  have eq3543501 : False := by grind
  exact eq3543501

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxy_x_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq18
  have eq31 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X2) (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq9
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X3 (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) X3 X2
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq9
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq9
    | exact resolve eq9 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq74
    | (have j0 := eq74 (σ X0) (σ X1)
       grind)
    | exact resolve eq74 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k X2 X0) = (M.op X2 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X0
       have i₂ := eq74 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq74 X0 (M.op X1 X1)
       grind)
    | exact superpose eq74 eq12
    | (have j0 := eq12 X2 X0
       have j1 := eq74 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq74 X1 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq74 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X1 X3 : G, (M.op X3 X3) = (M.op (M.op X1 (M.op X3 X3)) X3) := by
    intro X1 X3
    first
    | (have i₁ := eq56 x X3 (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq56
    | exact resolve eq56 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq118 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq127 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq90 X1 (M.op X1 (M.op X1 X1))
       have i₂ := eq64 X1 X1
       grind)
    | exact superpose eq64 eq90
    | exact resolve eq90 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq90
  have eq665 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X0 (M.op X0 X0) X2 X1
       have i₂ := eq127 X0 X0
       grind)
    | exact superpose eq127 eq61
    | exact resolve eq61 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq731 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq84 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq766 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X2) X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X1
       have i₂ := eq665 X1 X2 X0
       grind)
    | exact superpose eq665 eq58
    | exact resolve eq58 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq767 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X2 (M.op (M.op X0 X2) X1))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq127 X1 X3
       have i₂ := eq665 X1 X2 X0
       grind)
    | exact superpose eq665 eq127
    | exact resolve eq127 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq782 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op X3 X2) (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 (M.op X0 X1) X1 X3 X2
       have i₂ := eq665 X1 X1 X0
       grind)
    | exact superpose eq665 eq61
    | exact resolve eq61 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq798 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq782 X0 X1 x x
       have i₂ := eq61 X1 X1 x x
       grind)
    | exact superpose eq61 eq782
    | exact resolve eq782 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq902 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X1)) X1) = (M.op (M.op (M.op X2 (M.op X0 X1)) X1) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq766 X0 (M.op (M.op X2 (M.op X0 X1)) X1) X1
       have i₂ := eq766 X2 X1 (M.op X0 X1)
       grind)
    | exact superpose eq766 eq766
    | exact resolve eq766 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq921 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq902 X0 X1 X2
       have i₂ := eq798 (M.op X2 (M.op X0 X1)) X1
       grind)
    | exact superpose eq798 eq902
    | exact resolve eq902 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902
  have eq1102 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) = (M.op (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq766 X0 (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) (M.op X1 X2)
       have i₂ := eq767 X3 X2 (M.op X0 (M.op X1 X2)) X1
       grind)
    | exact superpose eq767 eq766
    | exact resolve eq766 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq1125 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1102 X0 X1 X2 X3
       have i₂ := eq798 (M.op X3 (M.op X0 (M.op X1 X2))) X2
       grind)
    | exact superpose eq798 eq1102
    | exact resolve eq1102 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1211 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77 x y
       grind)
    | exact superpose eq77 eq16
    | (have j1 := eq77 x y
       grind)
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1259 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X0) (σ X0)
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq31
    | (have j1 := eq77 X0 X1
       grind)
    | exact resolve eq31 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1440 : ∀ X0 X2 X3 : G, (M.op X2 (M.op (M.op X0 (M.op X3 X2)) (M.op X2 X2))) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq766 x X2 (M.op X0 (M.op X3 X2))
       have i₂ := eq1125 X0 X3 X2 x
       grind)
    | exact superpose eq1125 eq766
    | exact resolve eq766 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766 eq1125
  have eq1517 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq731 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq1518 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1517 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517
  have eq1524 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1518 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1518
    | exact resolve eq1518 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1525 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1518 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq1518
    | exact resolve eq1518 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq1526 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1525 X0
       have i₂ := eq1518 X0
       grind)
    | exact superpose eq1518 eq1525
    | exact resolve eq1525 eq1518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1525
  have eq1527 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1524 X0
       have i₂ := eq1518 X0
       grind)
    | exact superpose eq1518 eq1524
    | exact resolve eq1524 eq1518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518 eq1524
  have eq2476 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (M.op (M.op X1 (τ (M.op X0 X0))) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1440 X0 (τ X0) (τ X0)
       have i₂ := eq1526 X0
       grind)
    | exact superpose eq1526 eq1440
    | exact resolve eq1440 eq1526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440
  have eq2548 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq2476 X0 x
       have i₂ := eq798 x (τ (M.op X0 X0))
       grind)
    | exact superpose eq798 eq2476
    | exact resolve eq2476 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798 eq2476
  have eq2582 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq2548 X0
       have i₂ := eq1526 (M.op X0 X0)
       grind)
    | exact superpose eq1526 eq2548
    | exact resolve eq2548 eq1526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526 eq2548
  have eq2593 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq2582 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq2582
    | exact resolve eq2582 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2582
  have eq2612 : ∀ X0 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (M.op (σ X0) (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq2593 (σ X0)
       have i₂ := eq1527 X0
       grind)
    | exact superpose eq1527 eq2593
    | exact resolve eq2593 eq1527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2593
  have eq2647 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (σ (M.op X0 X0))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2612 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2612
    | exact resolve eq2612 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2612
  have eq3245 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1211
       have i₂ := eq1527 x
       grind)
    | exact superpose eq1527 eq1211
    | exact resolve eq1211 eq1527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq3366 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3245
       have i₂ := eq74 x y
       grind)
    | exact superpose eq74 eq3245
    | (have j1 := eq74 x y
       grind)
    | exact resolve eq3245 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq3245
  have eq3383 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq3366
  have eq3391 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq3383
       grind)
    | exact superpose eq3383 eq10
    | exact resolve eq10 eq3383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3383
  have eq3418 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3391
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq3391
    | exact resolve eq3391 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3391
  have eq3419 : y = (M.op x x) := by grind
  clear eq3418
  have eq3421 : ∀ X0 X1 : G, x = (M.op X1 (M.op (M.op X0 X1) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x X1 X0
       have i₂ := eq3419
       grind)
    | exact superpose eq3419 eq9
    | exact resolve eq9 eq3419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3423 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq58 x
       have i₂ := eq3419
       grind)
    | exact superpose eq3419 eq58
    | exact resolve eq58 eq3419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq3425 : x = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq118 x
       have i₂ := eq3419
       grind)
    | exact superpose eq3419 eq118
    | exact resolve eq118 eq3419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq3451 : x = (M.op x (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq2647 x
       have i₂ := eq3419
       grind)
    | exact superpose eq3419 eq2647
    | exact resolve eq2647 eq3419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2647
  have eq3454 : ∀ X0 X1 : G, y = (M.op X0 (M.op (M.op X1 X0) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 x x x x
       have i₂ := eq3419
       grind)
    | exact superpose eq3419 eq61
    | exact resolve eq61 eq3419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq3505 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq921 x y x
       have i₂ := eq3423
       grind)
    | exact superpose eq3423 eq921
    | exact resolve eq921 eq3423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921 eq3423
  have eq7909 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1259 X0 X1
       have i₂ := eq1527 X1
       grind)
    | exact superpose eq1527 eq1259
    | (have j0 := eq1259 X0 X1
       grind)
    | exact resolve eq1259 eq1527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259
  have eq8388 : x = (M.op x (τ (σ (k x y)))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3451
       have i₂ := eq7909 x y
       grind)
    | exact superpose eq7909 eq3451
    | (have j1 := eq7909 x y
       grind)
    | exact resolve eq3451 eq7909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3451 eq7909
  have eq8434 : x = (M.op x (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq8388
       have i₂ := eq10 (k x y)
       grind)
    | exact superpose eq10 eq8388
    | exact resolve eq8388 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8388
  have eq8461 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x (k x y)) := by
    first
    | (have i₁ := eq8434
       have i₂ := eq3505
       grind)
    | exact superpose eq3505 eq8434
    | exact resolve eq8434 eq3505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3505 eq8434
  have eq8467 : x = (M.op x (k x y)) := by
    first
    | (have r₁ := eq8461
       have r₂ := eq16
       grind)
    | exact resolve eq8461 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8461
  have eq8471 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8467
       have i₂ := eq3425
       grind)
    | exact superpose eq3425 eq8467
    | exact resolve eq8467 eq3425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3425 eq8467
  have eq8520 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8471
       have i₂ := eq3419
       grind)
    | exact superpose eq3419 eq8471
    | exact resolve eq8471 eq3419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3419 eq8471
  have eq8574 : ∀ X0 X1 : G, y = (M.op X0 (M.op (M.op X1 X0) y)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq3454 X0 X1
       have i₂ := eq8520
       grind)
    | exact superpose eq8520 eq3454
    | exact resolve eq3454 eq8520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3454 eq8520
  have eq8608 : x = y ∨ x = y := by
    first
    | (have i₁ := eq8574 x x
       have i₂ := eq3421 x x
       grind)
    | exact superpose eq3421 eq8574
    | exact resolve eq8574 eq3421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3421 eq8574
  have eq8609 : x = y := by grind
  clear eq8608
  have eq8611 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8609
       grind)
    | exact superpose eq8609 eq16
    | exact resolve eq16 eq8609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8609
  have eq8677 : False := by grind
  exact eq8677

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_x_pxy_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
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
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op y X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) (M.op x y))) := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
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
  have eq70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq10
    | exact resolve eq10 eq68
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
  clear eq72
  have eq75 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq70 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq70
    | exact resolve eq70 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ (M.op y x) = (M.op y y) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq91
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq97 : (M.op y x) = (M.op y y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq104 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq108 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq68 sF3
       grind)
    | exact superpose eq68 eq104
    | exact resolve eq104 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq110 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq68 y
       grind)
    | exact superpose eq68 eq108
    | exact resolve eq108 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq145 : ∀ X0 : G, (σ (k X0 (M.op y y))) = (k (σ X0) (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (M.op y y)
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq10
    | exact resolve eq10 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 : G, (M.op (M.op x y) (M.op y X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0) (σ X0)
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq14
    | exact resolve eq14 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq688 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 x
       have i₂ := eq55 X2 X0 X1 x
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq909 : ∀ X0 : G, (M.op y (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq238 eq50
    | exact resolve eq50 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq929 : ∀ X0 X1 X2 : G, (M.op (M.op X1 y) X0) = (M.op y (M.op (M.op X2 y) (M.op y (M.op (M.op x y) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq909 eq55
    | exact resolve eq55 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq931 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq929 X0 X1 x
       have i₂ := eq14 (M.op sF0 X0) y x
       grind)
    | exact superpose eq14 eq929
    | exact resolve eq929 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq1075 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq244 eq51
    | exact resolve eq51 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1095 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ y)) X0) = (M.op (σ y) (M.op (M.op X2 (σ y)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1075 eq55
    | exact resolve eq55 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1097 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1095 X0 X1 x
       have i₂ := eq14 (M.op sF4 X0) sF3 x
       grind)
    | exact superpose eq14 eq1095
    | exact resolve eq1095 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095
  have eq4862 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) (M.op X0 (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq244 eq249
    | exact resolve eq249 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq9792 : (σ (k (M.op y y) (M.op y y))) = (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq145 (M.op y y)
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq145
    | exact resolve eq145 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq145
  have eq9891 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (k (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq9792
       have i₂ := eq68 (M.op sF3 sF3)
       grind)
    | exact superpose eq68 eq9792
    | exact resolve eq9792 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9792
  have eq9899 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq9891
       have i₂ := eq68 (M.op y y)
       grind)
    | exact superpose eq68 eq9891
    | exact resolve eq9891 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq9891
  have eq9903 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq1097 eq9899
    | exact resolve eq9899 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097 eq9899
  have eq9906 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq244 eq9903
    | exact resolve eq9903 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244 eq9903
  have eq9907 : (σ (M.op (M.op x y) (M.op y y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq9906
       have i₂ := eq931 (M.op y y) y
       grind)
    | exact superpose eq931 eq9906
    | exact resolve eq9906 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931 eq9906
  have eq9908 : (σ (M.op y (M.op (M.op x y) y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq238 eq9907
    | exact resolve eq9907 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238 eq9907
  have eq9911 : (M.op y (M.op (M.op x y) y)) = (τ (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    first
    | exact superpose eq9908 eq16
    | exact resolve eq16 eq9908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68567 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq503 X0 (σ X0)
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq503
    | exact resolve eq503 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq68711 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq68567 X0
       have i₂ := eq75 (M.op X0 X0)
       grind)
    | exact superpose eq75 eq68567
    | exact resolve eq68567 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq68567
  have eq78148 : (σ x) = (M.op (σ x) (σ (M.op (M.op x x) (M.op x x)))) := by
    first
    | (have i₁ := eq68711 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq68711
    | (have j0 := eq68711 x
       grind)
    | exact resolve eq68711 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68711
  have eq79169 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ (M.op x (M.op (M.op X0 x) x)))) := by
    intro X0
    first
    | (have i₁ := eq78148
       have i₂ := eq55 x x X0 x
       grind)
    | exact superpose eq55 eq78148
    | exact resolve eq78148 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq78148
  have eq105661 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) (M.op y x))) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq14
    | exact resolve eq14 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq105851 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq105661 x
       have i₂ := eq14 x y x
       grind)
    | exact superpose eq14 eq105661
    | exact resolve eq105661 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105661
  have eq105991 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq105851 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq105851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105851
  have eq106004 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq26 eq105991
    | exact resolve eq105991 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105991
  have eq106017 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq106004
       have r₂ := eq27
       grind)
    | exact resolve eq106004 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106004
  have eq106067 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (σ y)) (M.op (σ y) (σ x)))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq106017 eq14
    | exact resolve eq14 eq106017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106017
  have eq106257 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq106067 x
       have i₂ := eq14 sF2 sF3 x
       grind)
    | exact superpose eq14 eq106067
    | exact resolve eq106067 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106067
  have eq106387 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq106257 eq51
    | exact resolve eq51 eq106257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq106257
  have eq107852 : (τ (σ x)) = (M.op y (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq106387 eq9911
    | exact resolve eq9911 eq106387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9911 eq106387
  have eq108096 : x = (M.op y (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq28 eq107852
    | exact resolve eq107852 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107852
  have eq110168 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq108096 eq909
    | exact resolve eq909 eq108096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909 eq108096
  have eq110304 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq110168
  have eq110529 : x = (M.op y (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq110304
       grind)
    | exact superpose eq110304 eq50
    | exact resolve eq50 eq110304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq110593 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq688 x y X0
       have i₂ := eq110304
       grind)
    | exact superpose eq110304 eq688
    | exact resolve eq688 eq110304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq110770 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq110529 eq9908
    | exact resolve eq9908 eq110529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9908 eq110529
  have eq111020 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq110770
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq110770
    | exact resolve eq110770 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110770
  have eq112578 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq111020 eq1075
    | exact resolve eq1075 eq111020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq112581 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op (σ x) X0))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq111020 eq4862
    | exact resolve eq4862 eq111020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4862 eq111020
  have eq120523 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq110593 x
       have i₂ := eq110304
       grind)
    | exact superpose eq110304 eq110593
    | exact resolve eq110593 eq110304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110304 eq110593
  have eq120663 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq120523
  have eq120737 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq120663
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq120663
    | exact resolve eq120663 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120663
  have eq120778 : ∀ X0 : G, y = (M.op (M.op X0 x) x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq120737 eq686
    | exact resolve eq686 eq120737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686 eq120737
  have eq121041 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq79169 x
       have i₂ := eq120778 x
       grind)
    | exact superpose eq120778 eq79169
    | exact resolve eq79169 eq120778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79169 eq120778
  have eq121313 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq121041
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq121041
    | exact resolve eq121041 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121041
  have eq121356 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq121313
    | exact resolve eq121313 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121313
  have eq140136 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq121356 eq112581
    | exact resolve eq112581 eq121356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112581 eq121356
  have eq140281 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq140136
  have eq140366 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq112578 eq140281
    | exact resolve eq140281 eq112578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112578 eq140281
  have eq140498 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq140366
  have eq140562 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq140498
    | exact resolve eq140498 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140498
  have eq140586 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq140562
       have r₂ := eq27
       grind)
    | exact resolve eq140562 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140562
  have eq140591 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq140586 eq29
    | exact resolve eq29 eq140586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq140586
  have eq140766 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq140591
    | exact resolve eq140591 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq140591
  have eq140767 : x = y := by grind
  clear eq140766
  have eq140786 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq140767
       grind)
    | exact superpose eq140767 eq18
    | exact resolve eq18 eq140767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq140787 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq140767
       grind)
    | exact superpose eq140767 eq24
    | exact resolve eq24 eq140767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq140767
  have eq140981 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq140787
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq140787
    | exact resolve eq140787 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq140787
  have eq141002 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq140981 eq26
    | exact resolve eq26 eq140981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq140981
  have eq141526 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq141002 eq73
    | exact resolve eq73 eq141002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq141002
  have eq141778 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq141526
       have i₂ := eq140786
       grind)
    | exact superpose eq140786 eq141526
    | exact resolve eq141526 eq140786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140786 eq141526
  have eq141824 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq141778 eq15
    | exact resolve eq15 eq141778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141778
  have eq141923 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq141824
    | exact resolve eq141824 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq141824
  have eq141950 : False := by grind
  exact eq141950

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pxy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq23 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq23 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq27 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq35 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 X0) (M.op X0 X1))) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 X0) (M.op X0 X1))) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq35 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq35 X1 X1 X2
       have r₂ := eq12 (M.op (M.op X2 X1) (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq35 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1 x
       have i₂ := eq9 X1 X0 x
       grind)
    | exact superpose eq9 eq47
    | (have j0 := eq47 X0 X1 x
       grind)
    | exact resolve eq47 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq61 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq24 (σ X0)
       grind)
    | exact superpose eq24 eq15
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq61
    | exact resolve eq61 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq61
  have eq178 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 x
       have i₂ := eq20 (M.op X1 X2) X1 x X0
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq711 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27 X0 X1
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq27
    | (have j0 := eq27 X0 X1
       have j1 := eq55 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq27 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq814 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq711 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq711
    | (have j0 := eq711 X0 X1
       grind)
    | exact resolve eq711 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq1131 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X1 (σ X0) (σ X0)
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq178
    | exact resolve eq178 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126102 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq814 x y
       grind)
    | exact superpose eq814 eq16
    | (have j1 := eq814 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq814 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq814 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq814 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq126557 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq126102
  have eq161365 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ (M.op x x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq178 X0 (σ x) (σ y)
       have i₂ := eq126557
       grind)
    | exact superpose eq126557 eq178
    | exact resolve eq178 eq126557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq126557
  have eq161515 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq161365 x
       have i₂ := eq1131 x x
       grind)
    | exact superpose eq1131 eq161365
    | exact resolve eq161365 eq1131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131 eq161365
  have eq196805 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq161515
       grind)
    | exact superpose eq161515 eq16
    | exact resolve eq16 eq161515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196813 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq161515
       grind)
    | exact superpose eq161515 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq161515
       grind)
    | exact resolve eq12 eq161515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161515
  have eq197039 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq196813
  have eq197138 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq197039
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq197039
    | exact resolve eq197039 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197039
  have eq308318 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq197138
       have i₂ := eq55 x y
       grind)
    | exact superpose eq55 eq197138
    | (have j1 := eq55 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq197138 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq197138
  have eq308399 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq308318
  have eq308420 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq308399
       have r₂ := eq196805
       grind)
    | exact resolve eq308399 eq196805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196805 eq308399
  have eq373814 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq308420
       grind)
    | exact superpose eq308420 eq10
    | exact resolve eq10 eq308420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308420
  have eq373884 : x = y ∨ x = y := by
    first
    | (have i₁ := eq373814
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq373814
    | exact resolve eq373814 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373814
  have eq373885 : x = y := by grind
  clear eq373884
  have eq427741 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq373885
       grind)
    | exact superpose eq373885 eq16
    | exact resolve eq16 eq373885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373885
  have eq427760 : False := by grind
  exact eq427760

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pyx_pyy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
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
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq87
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq87
    | exact resolve eq87 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq94 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq93
    | exact resolve eq93 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq109 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq109 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq109
    | (have j0 := eq109 (σ X0)
       grind)
    | exact resolve eq109 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq109 x
       grind)
    | exact superpose eq109 eq44
    | (have j1 := eq109 x
       grind)
    | exact resolve eq44 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq6211 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq381 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq76887 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) (M.op y x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq94
       grind)
    | exact superpose eq94 eq14
    | exact resolve eq14 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq77059 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq76887 x
       have i₂ := eq14 x y x
       grind)
    | exact superpose eq14 eq76887
    | exact resolve eq76887 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76887
  have eq77169 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq77059 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq77059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77170 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq77169
    | exact resolve eq77169 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77169
  have eq77181 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq77170
       have r₂ := eq28
       grind)
    | exact resolve eq77170 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77170
  have eq77203 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (σ y)) (M.op (σ y) (σ x)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq77181 eq14
    | exact resolve eq14 eq77181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77181
  have eq77361 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq77203 x
       have i₂ := eq14 sF2 sF3 x
       grind)
    | exact superpose eq14 eq77203
    | exact resolve eq77203 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77203
  have eq77479 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq77361
  have eq77609 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq77479
    | exact resolve eq77479 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77479
  have eq78741 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq77609 eq77059
    | exact resolve eq77059 eq77609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77059 eq77609
  have eq78743 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq78741
  have eq78745 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq78743
       have r₂ := eq28
       grind)
    | exact resolve eq78743 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78743
  have eq79774 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq385
       have i₂ := eq78745
       grind)
    | exact superpose eq78745 eq385
    | exact resolve eq385 eq78745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79795 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq78745
  have eq79893 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq79774
  have eq79929 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq79795
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq79795
    | exact resolve eq79795 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79795
  have eq79935 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq79893
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq79893
    | exact resolve eq79893 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79893
  have eq79992 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq79929
       grind)
    | exact superpose eq79929 eq72
    | exact resolve eq72 eq79929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq79929
  have eq80010 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq79992
    | exact resolve eq79992 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79992
  have eq80011 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq79935
       have i₂ := eq109 sF2
       grind)
    | exact superpose eq109 eq79935
    | (have j1 := eq109 (σ x)
       grind)
    | exact resolve eq79935 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118534 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq80011
  have eq118698 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq118534
    | exact resolve eq118534 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118534
  have eq118755 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq118698 eq80010
    | exact resolve eq80010 eq118698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80010 eq118698
  have eq118757 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq118755
  have eq118767 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq118757
       have r₂ := eq28
       grind)
    | exact resolve eq118757 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118757
  have eq120974 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq121501 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq120974 eq79935
    | exact resolve eq79935 eq120974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79935 eq120974
  have eq121516 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq121501
  have eq121526 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq121516 eq118767
    | exact resolve eq118767 eq121516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118767 eq121516
  have eq121660 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq121526
  have eq122570 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq121660 eq30
    | exact resolve eq30 eq121660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq121660
  have eq122746 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq122570
    | exact resolve eq122570 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq122570
  have eq122747 : x = y := by grind
  clear eq122746
  have eq122748 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq122747
       grind)
    | exact superpose eq122747 eq19
    | exact resolve eq19 eq122747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq122749 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq122747
       grind)
    | exact superpose eq122747 eq25
    | exact resolve eq25 eq122747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq122747
  have eq122923 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq122749
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq122749
    | exact resolve eq122749 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122749
  have eq122924 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq122923 eq27
    | exact resolve eq27 eq122923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq122923
  have eq123107 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq385
       have i₂ := eq122748
       grind)
    | exact superpose eq122748 eq385
    | exact resolve eq385 eq122748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq123144 : (M.op x (M.op x y)) = (k (M.op x y) x) := by grind
  have eq123322 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq123107
    | exact resolve eq123107 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123107
  have eq123384 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq127588 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq123322 eq109
    | (have j0 := eq109 (σ x)
       grind)
    | exact resolve eq109 eq123322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq127589 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122924 eq127588
    | exact resolve eq127588 eq122924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127588
  have eq127603 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq127589
       have r₂ := eq28
       grind)
    | exact resolve eq127589 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127589
  have eq127609 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122924 eq127603
    | exact resolve eq127603 eq122924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127603
  have eq127667 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127609 eq123384
    | exact resolve eq123384 eq127609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123384 eq127609
  have eq127673 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122924 eq127667
    | exact resolve eq127667 eq122924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127667
  have eq128246 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127673 eq123322
    | exact resolve eq123322 eq127673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123322 eq127673
  have eq128251 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq128246
  have eq128254 : x = (M.op x y) := by
    first
    | (have r₁ := eq128251
       have r₂ := eq28
       grind)
    | exact resolve eq128251 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128251
  have eq128265 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq128254 eq21
    | exact resolve eq21 eq128254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq128412 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq128254 eq123144
    | exact resolve eq123144 eq128254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123144
  have eq128420 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq128412
       have i₂ := eq122748
       grind)
    | exact superpose eq122748 eq128412
    | exact resolve eq128412 eq122748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122748 eq128412
  have eq128528 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq128265
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq128265
    | exact resolve eq128265 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128265
  have eq128532 : x = (k x x) := by
    first
    | exact superpose eq128254 eq128420
    | exact resolve eq128420 eq128254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128254 eq128420
  have eq131437 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6211 x
       have i₂ := eq128532
       grind)
    | exact superpose eq128532 eq6211
    | (have j0 := eq6211 x
       grind)
    | exact resolve eq6211 eq128532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6211 eq128532
  have eq131441 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq131437
  have eq131450 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq131441
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq131441
    | exact resolve eq131441 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq131441
  have eq131463 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq122924 eq131450
    | exact resolve eq131450 eq122924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122924 eq131450
  have eq131474 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq128528 eq131463
    | exact resolve eq131463 eq128528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128528 eq131463
  have eq131483 : False := by grind
  exact eq131483

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxx_pxy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (k (k (M.op X0 X0) X0) (M.op X0 X0)) = (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) := by
    intro X0
    grind
  have eq35 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    grind
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X0 X0)) (k (M.op X0 X0) X0))) := by
    intro X0 X1
    grind
  have eq37 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (k (M.op X0 X0) X0) (M.op (M.op X0 X0) X1))) = X1 := by
    intro X0 X1
    grind
  have eq39 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op (M.op X1 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (M.op X0 X0) X0) X0 X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq9
    | exact resolve eq9 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq116 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (k (M.op X0 X0) X0)) = (M.op (M.op X0 X0) (M.op (M.op X2 (M.op X0 X0)) (M.op X0 X0))) := by
    intro X0 X1 X2
    grind
  have eq137 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq25 X2 X0 X1 x
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 x
       have i₂ := eq25 (M.op X1 X2) X1 x X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X1) X2) = (M.op X1 (M.op (M.op X3 X1) (M.op (M.op X0 X1) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op (M.op X4 X1) X2) X1 X3
       have i₂ := eq25 X2 X1 X4 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (k (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq116 X0 X1 x
       have i₂ := eq39 (M.op X0 X0) x
       grind)
    | exact superpose eq39 eq116
    | exact resolve eq116 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq157 : ∀ X0 X1 : G, (k (k (M.op X0 X0) X0) (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (k (M.op X0 X0) X0)) := by
    intro X0 X1
    grind
  clear eq156
  have eq167 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) (M.op (M.op X2 X1) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq137 X1 X2 (M.op (M.op X3 (M.op X2 X1)) (M.op (M.op X2 X1) X0))
       have i₂ := eq9 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq9 eq137
    | exact resolve eq137 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq137 X1 X2 (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0))
       have i₂ := eq137 (M.op X2 X1) X3 X0
       grind)
    | exact superpose eq137 eq137
    | exact resolve eq137 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op X1 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq137 X1 X0 (k (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1))
       have i₂ := eq35 (M.op X0 X1)
       grind)
    | exact superpose eq35 eq137
    | exact resolve eq137 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) X0) = (M.op X2 (M.op (M.op X4 X2) (M.op X2 (M.op (M.op X3 X2) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 (M.op X2 (M.op (M.op X3 X2) X0)) X2 X4 X1
       have i₂ := eq137 X2 X3 X0
       grind)
    | exact superpose eq137 eq25
    | exact resolve eq25 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X3 X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq176 X0 X1 X2 X3 x
       have i₂ := eq9 (M.op (M.op X3 X2) X0) X2 x
       grind)
    | exact superpose eq9 eq176
    | exact resolve eq176 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq191 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (k (M.op X1 X1) X1) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq137 X1 X1 (M.op (k (M.op X1 X1) X1) (M.op (M.op X1 X1) X0))
       have i₂ := eq37 X1 X0
       grind)
    | exact superpose eq37 eq137
    | exact resolve eq137 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 (M.op X2 X2)) (M.op (k (M.op X2 X2) X2) (M.op (M.op X2 X2) X0)))) = (M.op (M.op X1 (M.op X2 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 (M.op (k (M.op X2 X2) X2) (M.op (M.op X2 X2) X0)) (M.op X2 X2) X3 X1
       have i₂ := eq37 X2 X0
       grind)
    | exact superpose eq37 eq25
    | exact resolve eq25 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq200 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) X0) = (M.op X2 (M.op X2 (M.op (k (M.op X2 X2) X2) (M.op (M.op X2 X2) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq196 X0 X1 X2 x
       have i₂ := eq169 (M.op (k (M.op X2 X2) X2) (M.op (M.op X2 X2) X0)) X2 X2 x
       grind)
    | exact superpose eq169 eq196
    | exact resolve eq196 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq209 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) X0) = (M.op X2 (M.op X2 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq200 X0 X1 X2
       have i₂ := eq191 X0 X2
       grind)
    | exact superpose eq191 eq200
    | exact resolve eq200 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq200
  have eq229 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq146 X1 X0 (k (M.op X0 X0) X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq146
    | exact resolve eq146 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X2 X3)) (M.op X3 (M.op X3 X0)))) = (M.op (M.op X1 (M.op X2 X3)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 (M.op X3 (M.op X3 X0)) (M.op X2 X3) X4 X1
       have i₂ := eq146 X2 X3 X0
       grind)
    | exact superpose eq146 eq25
    | exact resolve eq25 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op (M.op X2 (M.op X2 X0)) X3)) = (M.op (M.op X2 (M.op X2 X0)) (M.op (M.op X4 (M.op X2 (M.op X2 X0))) X3)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq25 X3 (M.op X2 (M.op X2 X0)) X4 (M.op x X2)
       have i₂ := eq146 x X2 X0
       grind)
    | exact superpose eq146 eq25
    | exact resolve eq25 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X2 X0)) X3)) = (M.op (M.op X2 X0) (M.op (M.op X2 X0) X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq242 X0 X2 X3 x
       have i₂ := eq169 X3 (M.op X2 X0) X2 x
       grind)
    | exact superpose eq169 eq242
    | exact resolve eq242 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq246 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) X0) = (M.op X3 (M.op X3 (M.op X3 (M.op X3 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq241 X0 X1 X2 X3 x
       have i₂ := eq169 (M.op X3 (M.op X3 X0)) X3 X2 x
       grind)
    | exact superpose eq169 eq241
    | exact resolve eq241 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq274 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X3 (M.op X0 X0)) (M.op (M.op X2 (M.op X0 X0)) (k (M.op X0 X0) X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 (M.op (M.op X2 (M.op X0 X0)) (k (M.op X0 X0) X0)) (M.op X0 X0) X3 X1
       have i₂ := eq36 X0 X2
       grind)
    | exact superpose eq36 eq25
    | exact resolve eq25 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op X2 (M.op X0 X0)) (k (M.op X0 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq146 X1 (M.op X0 X0) (M.op (M.op X2 (M.op X0 X0)) (k (M.op X0 X0) X0))
       have i₂ := eq36 X0 X2
       grind)
    | exact superpose eq36 eq146
    | exact resolve eq146 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq279 : ∀ X0 X1 : G, (k (k (M.op X0 X0) X0) (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq278 X0 X1 x
       have i₂ := eq157 X0 x
       grind)
    | exact superpose eq157 eq278
    | exact resolve eq278 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq283 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) = (M.op X0 (M.op X0 (M.op (M.op X2 (M.op X0 X0)) (k (M.op X0 X0) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq274 X0 X1 X2 x
       have i₂ := eq169 (M.op (M.op X2 (M.op X0 X0)) (k (M.op X0 X0) X0)) X0 X0 x
       grind)
    | exact superpose eq169 eq274
    | exact resolve eq274 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169 eq274
  have eq297 : ∀ X0 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = (k (k (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq279 X0 x
       have i₂ := eq229 (M.op X0 X0) x
       grind)
    | exact superpose eq229 eq279
    | exact resolve eq279 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq301 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) = (M.op X0 (M.op X0 (k (k (M.op X0 X0) X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq283 X0 X1 x
       have i₂ := eq157 X0 x
       grind)
    | exact superpose eq157 eq283
    | exact resolve eq283 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq283
  have eq305 : ∀ X0 : G, (k (k (M.op X0 X0) X0) (M.op X0 X0)) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq297 X0
       have i₂ := eq170 X0 X0
       grind)
    | exact superpose eq170 eq297
    | exact resolve eq297 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq346 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X1 (M.op X2 (M.op X2 X0))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq179 X3 X1 (M.op X2 (M.op X2 X0)) (M.op x X2)
       have i₂ := eq146 x X2 X0
       grind)
    | exact superpose eq146 eq179
    | exact resolve eq179 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq349 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X1 (k (M.op X0 X0) X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 X2 X1 (k (M.op X0 X0) X0) X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq179
    | exact resolve eq179 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 X1)) X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq137 (M.op X3 X1) X2 X4
       have i₂ := eq179 (M.op (M.op X2 (M.op X3 X1)) X4) X3 X1 X0
       grind)
    | (have i₁ := eq137 (M.op X3 X1) X2 X4
       have i₂ := eq179 (M.op (M.op X2 (M.op X3 X1)) X4) X0 X1 X3
       grind)
    | exact superpose eq179 eq137
    | exact resolve eq137 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq421 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 X1)) X4)) = (M.op (M.op X5 (M.op X3 X1)) (M.op (M.op X3 X1) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq25 X4 (M.op X3 X1) X2 X5
       have i₂ := eq179 (M.op (M.op X2 (M.op X3 X1)) X4) X3 X1 X0
       grind)
    | (have i₁ := eq25 X4 (M.op X3 X1) X2 X5
       have i₂ := eq179 (M.op (M.op X2 (M.op X3 X1)) X4) X0 X1 X3
       grind)
    | exact superpose eq179 eq25
    | exact resolve eq25 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq428 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 X1)) X4)) = (M.op X1 (M.op X1 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq421 X0 X1 X2 X3 X4 x
       have i₂ := eq167 X4 X1 X3 x
       grind)
    | exact superpose eq167 eq421
    | exact resolve eq421 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq626 : ∀ X0 : G, (k (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)) = (M.op (k (M.op X0 X0) X0) (M.op X0 (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq39 (k (M.op X0 X0) X0) X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq39
    | exact resolve eq39 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq666 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) X0) = (k (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq626 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq626
    | exact resolve eq626 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq682 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) X0) = (k (k (k (M.op X0 X0) X0) (M.op X0 X0)) (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq666 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq666
    | exact resolve eq666 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq690 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) X0) = (k (M.op X0 (M.op X0 (M.op X0 X0))) (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq682 X0
       have i₂ := eq305 X0
       grind)
    | exact superpose eq305 eq682
    | exact resolve eq682 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq716 : ∀ X0 : G, (k (k (k (M.op X0 X0) X0) (M.op X0 X0)) (k (M.op X0 X0) X0)) = (M.op (k (k (M.op X0 X0) X0) (M.op X0 X0)) (k (k (M.op X0 X0) X0) (M.op X0 X0))) := by
    intro X0
    grind
  have eq748 : ∀ X0 : G, (k (M.op X0 (M.op X0 (M.op X0 X0))) (k (M.op X0 X0) X0)) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq716 X0
       have i₂ := eq305 X0
       grind)
    | exact superpose eq305 eq716
    | exact resolve eq716 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq770 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))) = (k (M.op X0 (M.op X0 (M.op X0 X0))) (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq748 X0
       have i₂ := eq346 X0 X0 X0 (M.op X0 (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq346 eq748
    | exact resolve eq748 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq780 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) X0) = (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq770 X0
       have i₂ := eq690 X0
       grind)
    | exact superpose eq690 eq770
    | exact resolve eq770 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq1185 : ∀ X0 X1 X2 : G, (M.op (k (M.op X0 X0) X0) X1) = (M.op (M.op X2 (k (k (k (M.op X0 X0) X0) (M.op X0 X0)) (k (M.op X0 X0) X0))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq349 (k (M.op X0 X0) X0) X2 X1
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq349
    | exact resolve eq349 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq1294 : ∀ X0 X1 X2 : G, (M.op (k (M.op X0 X0) X0) X1) = (M.op (M.op X2 (k (M.op X0 (M.op X0 (M.op X0 X0))) (k (M.op X0 X0) X0))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1185 X0 X1 X2
       have i₂ := eq305 X0
       grind)
    | exact superpose eq305 eq1185
    | exact resolve eq1185 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq1312 : ∀ X0 X1 X2 : G, (M.op (k (M.op X0 X0) X0) X1) = (M.op (M.op X2 (M.op (k (M.op X0 X0) X0) X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1294 X0 X1 X2
       have i₂ := eq690 X0
       grind)
    | exact superpose eq690 eq1294
    | exact resolve eq1294 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294
  have eq1319 : ∀ X0 X1 : G, (M.op (k (M.op X0 X0) X0) X1) = (M.op X0 (M.op X0 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1312 X0 X1 x
       have i₂ := eq246 X1 x (k (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq246 eq1312
    | exact resolve eq1312 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq1312
  have eq1850 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq59 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq59 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq59 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq59 X0 X1
       grind)
    | exact resolve eq13 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq1937 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1850 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850
  have eq1938 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1937 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1937
  have eq1958 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1938 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1938
    | (have j0 := eq1938 X0 X1
       grind)
    | exact resolve eq1938 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1938
  have eq1959 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1958 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958
  have eq3828 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X0 X0))) X3))))) = (M.op (M.op X4 (M.op X2 (M.op X0 X0))) (M.op (M.op X2 (M.op X0 X0)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 X3 (M.op X2 (M.op X0 X0)) X1 X4
       have i₂ := eq209 (M.op (M.op X1 (M.op X2 (M.op X0 X0))) X3) X2 X0
       grind)
    | exact superpose eq209 eq25
    | exact resolve eq25 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq3910 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) X3)) = (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X0 X0))) X3))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3828 X0 X1 X2 X3 x
       have i₂ := eq167 X3 (M.op X0 X0) X2 x
       grind)
    | exact superpose eq167 eq3828
    | exact resolve eq3828 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167 eq3828
  have eq4083 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) X3)) = (M.op (k (M.op X0 X0) X0) (M.op (M.op X1 (M.op X2 (M.op X0 X0))) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3910 X0 X1 X2 X3
       have i₂ := eq1319 X0 (M.op (M.op X1 (M.op X2 (M.op X0 X0))) X3)
       grind)
    | exact superpose eq1319 eq3910
    | exact resolve eq3910 eq1319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3910
  have eq4194 : ∀ X0 X1 X2 X3 : G, (M.op (k (M.op X0 X0) X0) (M.op (M.op X1 (M.op X2 (M.op X0 X0))) X3)) = (M.op X0 (M.op (M.op X0 (M.op X0 X0)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4083 X0 X1 X2 X3
       have i₂ := eq245 X0 X0 X3
       grind)
    | exact superpose eq245 eq4083
    | exact resolve eq4083 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq4083
  have eq5797 : ∀ X0 X1 : G, (M.op X0 X0) = (σ X1) ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1959 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1959
    | exact resolve eq1959 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1959
  have eq5980 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5797 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq5797
    | (have j0 := eq5797 X0 X1
       grind)
    | exact resolve eq5797 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq5797
  have eq6634 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5980 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5980
    | exact resolve eq5980 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6742 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq5980 X0 X1
       grind)
    | exact superpose eq5980 eq10
    | (have j1 := eq5980 X0 X1
       grind)
    | exact resolve eq10 eq5980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5980
  have eq7202 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X2))) X3) = (M.op X2 (M.op X2 (M.op X2 (M.op X2 (M.op (M.op X4 (M.op X1 (M.op X2 X2))) (M.op (M.op X5 (M.op X1 (M.op X2 X2))) (M.op (M.op X1 (M.op X2 X2)) X3))))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq209 (M.op (M.op X4 (M.op X1 (M.op X2 X2))) (M.op (M.op X5 (M.op X1 (M.op X2 X2))) (M.op (M.op X1 (M.op X2 X2)) X3))) X1 X2
       have i₂ := eq148 X5 (M.op X1 (M.op X2 X2)) X3 X4 X0
       grind)
    | exact superpose eq148 eq209
    | exact resolve eq209 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq209
  have eq7213 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X2))) X3) = (M.op (k (M.op X2 X2) X2) (M.op (M.op X4 (M.op X1 (M.op X2 X2))) (M.op (M.op X5 (M.op X1 (M.op X2 X2))) (M.op (M.op X1 (M.op X2 X2)) X3)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq7202 X0 X1 X2 X3 X4 X5
       have i₂ := eq1319 X2 (M.op (M.op X4 (M.op X1 (M.op X2 X2))) (M.op (M.op X5 (M.op X1 (M.op X2 X2))) (M.op (M.op X1 (M.op X2 X2)) X3)))
       grind)
    | exact superpose eq1319 eq7202
    | exact resolve eq7202 eq1319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319 eq7202
  have eq7474 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X2))) X3) = (M.op X2 (M.op (M.op X2 (M.op X2 X2)) (M.op (M.op X5 (M.op X1 (M.op X2 X2))) (M.op (M.op X1 (M.op X2 X2)) X3)))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq7213 X0 X1 X2 X3 x X5
       have i₂ := eq4194 X2 x X1 (M.op (M.op X5 (M.op X1 (M.op X2 X2))) (M.op (M.op X1 (M.op X2 X2)) X3))
       grind)
    | exact superpose eq4194 eq7213
    | exact resolve eq7213 eq4194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4194 eq7213
  have eq7639 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X2))) X3) = (M.op X2 (M.op (M.op X2 X2) (M.op (M.op X2 X2) (M.op (M.op X1 (M.op X2 X2)) X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7474 X0 X1 X2 X3 x
       have i₂ := eq428 X2 (M.op X2 X2) x X1 (M.op (M.op X1 (M.op X2 X2)) X3)
       grind)
    | exact superpose eq428 eq7474
    | exact resolve eq7474 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428 eq7474
  have eq7732 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 (M.op X1 (M.op X2 X2))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7639 X0 X1 X2 X3
       have i₂ := eq420 X2 X2 X1 X2 X3
       grind)
    | exact superpose eq420 eq7639
    | exact resolve eq7639 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420 eq7639
  have eq7945 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq229 X1 X1
       have i₂ := eq6634 X0 X1
       grind)
    | (have i₁ := eq229 X0 X1
       have i₂ := eq6634 (M.op X1 X0) X1
       grind)
    | exact superpose eq6634 eq229
    | (have j1 := eq6634 (k X0 X1) X0
       grind)
    | exact resolve eq229 eq6634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq10165 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq7945 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7945
  have eq10376 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10165 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10165
  have eq11313 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq10376 (σ X0)
       grind)
    | exact superpose eq10376 eq15
    | exact resolve eq15 eq10376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11328 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11313 X0
       have i₂ := eq10376 X0
       grind)
    | exact superpose eq10376 eq11313
    | exact resolve eq11313 eq10376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10376 eq11313
  have eq12874 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (k (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 (σ X0)
       have i₂ := eq11328 X0
       grind)
    | exact superpose eq11328 eq35
    | exact resolve eq35 eq11328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq12893 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X1) = (M.op (M.op X2 (M.op X3 (σ (M.op X0 X0)))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7732 X2 X3 (σ X0) X1
       have i₂ := eq11328 X0
       grind)
    | exact superpose eq11328 eq7732
    | exact resolve eq7732 eq11328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7732
  have eq12917 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq137 (σ X0) (σ X0) X1
       have i₂ := eq11328 X0
       grind)
    | exact superpose eq11328 eq137
    | exact resolve eq137 eq11328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq12969 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq12874 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq12874
    | exact resolve eq12874 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12874
  have eq15061 : ∀ X0 : G, (k (M.op (σ (k (M.op X0 X0) X0)) (σ (k (M.op X0 X0) X0))) (σ (k (M.op X0 X0) X0))) = (M.op (σ (k (M.op X0 X0) X0)) (M.op (σ X0) (σ (k (M.op X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq39 (σ (k (M.op X0 X0) X0)) (σ X0)
       have i₂ := eq12969 X0
       grind)
    | exact superpose eq12969 eq39
    | exact resolve eq39 eq12969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq15112 : ∀ X0 : G, (M.op (σ (k (M.op X0 X0) X0)) (σ X0)) = (k (M.op (σ (k (M.op X0 X0) X0)) (σ (k (M.op X0 X0) X0))) (σ (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq15061 X0
       have i₂ := eq12969 X0
       grind)
    | exact superpose eq12969 eq15061
    | exact resolve eq15061 eq12969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12969 eq15061
  have eq15152 : ∀ X0 : G, (M.op (σ (k (M.op X0 X0) X0)) (σ X0)) = (k (σ (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0))) (σ (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq15112 X0
       have i₂ := eq11328 (k (M.op X0 X0) X0)
       grind)
    | exact superpose eq11328 eq15112
    | exact resolve eq15112 eq11328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15112
  have eq15171 : ∀ X0 : G, (M.op (σ (k (M.op X0 X0) X0)) (σ X0)) = (σ (k (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq15152 X0
       have i₂ := eq15 (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)
       grind)
    | exact superpose eq15 eq15152
    | exact resolve eq15152 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15152
  have eq15179 : ∀ X0 : G, (M.op (σ (k (M.op X0 X0) X0)) (σ X0)) = (σ (k (k (k (M.op X0 X0) X0) (M.op X0 X0)) (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq15171 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq15171
    | exact resolve eq15171 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq15171
  have eq15183 : ∀ X0 : G, (M.op (σ (k (M.op X0 X0) X0)) (σ X0)) = (σ (k (M.op X0 (M.op X0 (M.op X0 X0))) (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq15179 X0
       have i₂ := eq305 X0
       grind)
    | exact superpose eq305 eq15179
    | exact resolve eq15179 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15179
  have eq15186 : ∀ X0 : G, (M.op (σ (k (M.op X0 X0) X0)) (σ X0)) = (σ (M.op (k (M.op X0 X0) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq15183 X0
       have i₂ := eq690 X0
       grind)
    | exact superpose eq690 eq15183
    | exact resolve eq15183 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690 eq15183
  have eq40544 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (k (k (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) (σ (M.op X1 X1))) (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))))) = (M.op (σ X1) (M.op (σ X1) (M.op (M.op X0 (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1)))) (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq12917 X1 (M.op (σ (M.op X1 X1)) (k (k (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) (σ (M.op X1 X1))) (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1)))))
       have i₂ := eq301 (σ (M.op X1 X1)) X0
       grind)
    | exact superpose eq301 eq12917
    | exact resolve eq12917 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq40567 : ∀ X1 : G, (M.op (σ (M.op X1 X1)) (k (k (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) (σ (M.op X1 X1))) (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))))) = (M.op (σ X1) (M.op (σ X1) (M.op (σ X1) (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1)))))) := by
    intro X1
    first
    | (have i₁ := eq40544 x X1
       have i₂ := eq12893 X1 (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) x (σ (M.op X1 X1))
       grind)
    | exact superpose eq12893 eq40544
    | exact resolve eq40544 eq12893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12893 eq40544
  have eq40885 : ∀ X1 : G, (M.op (σ X1) (σ (M.op X1 X1))) = (M.op (σ (M.op X1 X1)) (k (k (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) (σ (M.op X1 X1))) (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))))) := by
    intro X1
    first
    | (have i₁ := eq40567 X1
       have i₂ := eq12917 X1 (σ (M.op X1 X1))
       grind)
    | exact superpose eq12917 eq40567
    | exact resolve eq40567 eq12917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12917 eq40567
  have eq41177 : ∀ X1 : G, (M.op (σ X1) (σ (M.op X1 X1))) = (M.op (σ (M.op X1 X1)) (M.op (σ (M.op X1 X1)) (M.op (σ (M.op X1 X1)) (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1)))))) := by
    intro X1
    first
    | (have i₁ := eq40885 X1
       have i₂ := eq305 (σ (M.op X1 X1))
       grind)
    | exact superpose eq305 eq40885
    | exact resolve eq40885 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq40885
  have eq41394 : ∀ X1 : G, (M.op (σ X1) (σ (M.op X1 X1))) = (M.op (k (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) (σ (M.op X1 X1))) (σ (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq41177 X1
       have i₂ := eq780 (σ (M.op X1 X1))
       grind)
    | exact superpose eq780 eq41177
    | exact resolve eq41177 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780 eq41177
  have eq41562 : ∀ X1 : G, (M.op (σ X1) (σ (M.op X1 X1))) = (M.op (k (σ (M.op (M.op X1 X1) (M.op X1 X1))) (σ (M.op X1 X1))) (σ (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq41394 X1
       have i₂ := eq11328 (M.op X1 X1)
       grind)
    | exact superpose eq11328 eq41394
    | exact resolve eq41394 eq11328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41394
  have eq41687 : ∀ X1 : G, (M.op (σ X1) (σ (M.op X1 X1))) = (M.op (σ (k (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 X1))) (σ (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq41562 X1
       have i₂ := eq15 (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 X1)
       grind)
    | exact superpose eq15 eq41562
    | exact resolve eq41562 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41562
  have eq41774 : ∀ X1 : G, (M.op (σ X1) (σ (M.op X1 X1))) = (σ (M.op (k (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 X1)) (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq41687 X1
       have i₂ := eq15186 (M.op X1 X1)
       grind)
    | exact superpose eq15186 eq41687
    | exact resolve eq41687 eq15186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15186 eq41687
  have eq41831 : ∀ X1 : G, (M.op (σ X1) (σ (M.op X1 X1))) = (σ (M.op (M.op X1 (M.op X1 (M.op X1 X1))) (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq41774 X1
       have i₂ := eq170 X1 X1
       grind)
    | exact superpose eq170 eq41774
    | exact resolve eq41774 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq41774
  have eq41871 : ∀ X1 : G, (M.op (σ X1) (σ (M.op X1 X1))) = (σ (M.op X1 (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq41831 X1
       have i₂ := eq346 X1 X1 X1 (M.op X1 X1)
       grind)
    | exact superpose eq346 eq41831
    | exact resolve eq41831 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq41831
  have eq59314 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6742 (σ X0) X1
       have i₂ := eq11328 X0
       grind)
    | exact superpose eq11328 eq6742
    | (have j0 := eq6742 (σ X0) X1
       grind)
    | exact resolve eq6742 eq11328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6742 eq11328
  have eq59407 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59314 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq59314
    | (have j0 := eq59314 X0 X1
       grind)
    | exact resolve eq59314 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59314
  have eq59443 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq59407 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq59407
    | (have j0 := eq59407 X0 X1
       grind)
    | exact resolve eq59407 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59407
  have eq132338 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59443 x y
       grind)
    | exact superpose eq59443 eq16
    | (have j1 := eq59443 x y
       grind)
    | exact resolve eq16 eq59443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59443
  have eq135428 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq132338
       have i₂ := eq6634 y x
       grind)
    | exact superpose eq6634 eq132338
    | (have j1 := eq6634 y x
       grind)
    | exact resolve eq132338 eq6634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6634 eq132338
  have eq135434 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq135428
  have eq135435 : y = (M.op x x) := by grind
  clear eq135434
  have eq136294 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41871 x
       have i₂ := eq135435
       grind)
    | exact superpose eq135435 eq41871
    | exact resolve eq41871 eq135435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41871 eq135435
  have eq136463 : False := by grind
  exact eq136463
