import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation419 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law419 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  clear eq18
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq467 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq37
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq37 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq3310 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq467 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq467
    | exact resolve eq467 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3352 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (k y (τ (σ x))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq467 (σ x) y
       grind)
    | exact superpose eq467 eq16
    | (have j1 := eq467 (σ x) y
       grind)
    | (have r₁ := eq16
       have r₂ := eq467 (M.op (σ x) (σ y)) (M.op x y)
       grind)
    | exact resolve eq16 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq3365 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y (τ (σ x))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3352
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq3352
    | exact resolve eq3352 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3352
  have eq3372 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3310 X0 X1
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq3310
    | (have j0 := eq3310 X0 X1
       grind)
    | exact resolve eq3310 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq3310
  have eq3377 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3365
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3365
    | exact resolve eq3365 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3365
  have eq3398 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq3372 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq3372 X0 X1
       grind)
    | exact superpose eq3372 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq3372 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq3372 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq3372 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq3372 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq3372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3437 : ∀ X0 X1 : G, (τ (k X1 (τ X0))) = (τ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0
       have i₂ := eq3372 X1 (τ X0)
       grind)
    | (have i₁ := eq30 X0
       have i₂ := eq3372 (τ X0) (τ X0)
       grind)
    | exact superpose eq3372 eq30
    | (have j1 := eq3372 X1 (τ X0)
       grind)
    | exact resolve eq30 eq3372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3372
  have eq3444 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3398 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3398
  have eq3445 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3444 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3444
  have eq3539 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq3445 X0 X1
       grind)
    | exact superpose eq3445 eq11
    | (have j1 := eq3445 X0 X1
       grind)
    | exact resolve eq11 eq3445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3445
  have eq3655 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3539 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq3539
    | (have j0 := eq3539 X0 X1
       grind)
    | exact resolve eq3539 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3539
  have eq3675 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3655 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3655
    | (have j0 := eq3655 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq3655 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3655
  have eq3833 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3675 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq3675
    | (have j0 := eq3675 X0 X1
       grind)
    | exact resolve eq3675 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3675
  have eq13048 : ∀ X0 X1 : G, (k X1 (τ X0)) = (σ (τ (M.op (τ X0) X1))) ∨ (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 (τ X0))
       have i₂ := eq3437 X0 X1
       grind)
    | exact superpose eq3437 eq11
    | (have j1 := eq3437 X0 X1
       grind)
    | exact resolve eq11 eq3437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3437
  have eq13177 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13048 X0 X1
       have i₂ := eq11 (M.op (τ X0) X1)
       grind)
    | exact superpose eq11 eq13048
    | (have j0 := eq13048 X0 X1
       grind)
    | exact resolve eq13048 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13048
  have eq14141 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq13177 X0 X1
       grind)
    | exact superpose eq13177 eq19
    | (have j1 := eq13177 X0 X1
       grind)
    | exact resolve eq19 eq13177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq13177
  have eq14258 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14141 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14141
    | exact resolve eq14141 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14141
  have eq14361 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14258 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq14258
    | (have j0 := eq14258 X0 X1
       grind)
    | exact resolve eq14258 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14258
  have eq14373 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14361 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq14361
    | (have j0 := eq14361 X0 X1
       grind)
    | exact resolve eq14361 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14361
  have eq17902 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3833 y x
       grind)
    | exact superpose eq3833 eq16
    | (have j1 := eq3833 y x
       grind)
    | exact resolve eq16 eq3833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3833
  have eq18003 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq17902
       have i₂ := eq14373 x y
       grind)
    | exact superpose eq14373 eq17902
    | (have j1 := eq14373 x y
       grind)
    | (have r₁ := eq17902
       have r₂ := eq14373 x y
       grind)
    | (have r₁ := eq17902
       have r₂ := eq14373 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq17902
       have r₂ := eq14373 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq17902 eq14373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14373 eq17902
  have eq18008 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18003
  have eq18009 : x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq18008
  have eq18017 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18009
       grind)
    | exact superpose eq18009 eq16
    | exact resolve eq16 eq18009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18009
  have eq18018 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq18017
       have r₂ := eq22 x
       grind)
    | exact resolve eq18017 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18017
  have eq18020 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq18018
       grind)
    | exact superpose eq18018 eq10
    | exact resolve eq10 eq18018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18018
  have eq18083 : x = y ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq18020
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18020
    | exact resolve eq18020 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18020
  have eq18085 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18083
       grind)
    | exact superpose eq18083 eq16
    | exact resolve eq16 eq18083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18083
  have eq18086 : (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq18085
       have r₂ := eq22 x
       grind)
    | exact resolve eq18085 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18085
  have eq18087 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3377
       have i₂ := eq18086
       grind)
    | exact superpose eq18086 eq3377
    | (have r₁ := eq3377
       have r₂ := eq18086
       grind)
    | exact resolve eq3377 eq18086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3377
  have eq18088 : (M.op x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq18086
       grind)
    | exact superpose eq18086 eq10
    | exact resolve eq10 eq18086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18132 : (σ x) = (σ y) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq18087
  have eq18152 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18088
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq18088
    | exact resolve eq18088 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18088
  have eq18155 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18152
       grind)
    | exact superpose eq18152 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq18152
       grind)
    | exact resolve eq13 eq18152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18152
  have eq18160 : x = y ∨ (k y x) = (M.op x x) := by grind
  clear eq18155
  have eq18162 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18160
       grind)
    | exact superpose eq18160 eq16
    | exact resolve eq16 eq18160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18160
  have eq18163 : (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq18162
       have r₂ := eq22 x
       grind)
    | exact resolve eq18162 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18162
  have eq19525 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18132
       grind)
    | exact superpose eq18132 eq16
    | exact resolve eq16 eq18132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18132
  have eq19613 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq19525
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq19525
    | exact resolve eq19525 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq19525
  have eq19634 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq19613
       have r₂ := eq18086
       grind)
    | exact resolve eq19613 eq18086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19613
  have eq19635 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq19634
       have i₂ := eq18163
       grind)
    | exact superpose eq18163 eq19634
    | exact resolve eq19634 eq18163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18163 eq19634
  have eq19653 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq19635
       grind)
    | exact superpose eq19635 eq11
    | exact resolve eq11 eq19635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19635
  have eq19756 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19653
       grind)
    | exact superpose eq19653 eq16
    | exact resolve eq16 eq19653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19653
  have eq19786 : False := by grind
  exact eq19786

/-- `Equation4209`: `x ◇ y = ((z ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pxx_pxy_pyx_Equation4209 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4209 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4209.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X2 X1) X0) X1) := by
    intro X0 X1 X2
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
  have eq51 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op (M.op x y) X0) y) := by
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
  have eq52 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op x X1)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (k (M.op X0 X0) X0) X0) := by
    intro X0
    grind
  have eq66 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op (k (M.op X0 X0) X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq37 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq86 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq86
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq86
    | exact resolve eq86 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq92
    | exact resolve eq92 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
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
  have eq107 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (k y x) = (M.op y x) := by
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
  have eq108 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : (M.op y x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq54 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq54
    | (have j0 := eq54 x y
       grind)
    | exact resolve eq54 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : (M.op (σ y) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq54
    | (have j0 := eq54 (σ x) (σ y)
       grind)
    | exact resolve eq54 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op X1 X0) X1
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq110 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq110
    | (have j0 := eq110 (σ X0)
       grind)
    | exact resolve eq110 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq110 x
       grind)
    | exact superpose eq110 eq44
    | (have j1 := eq110 x
       grind)
    | exact resolve eq44 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq353 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq110 y
       grind)
    | exact superpose eq110 eq74
    | (have j1 := eq110 y
       grind)
    | exact resolve eq74 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq366 : ∀ X0 : G, (M.op X0 X0) = (M.op (k (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq65
    | exact resolve eq65 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq506 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0 X0
       have i₂ := eq366 X0
       grind)
    | exact superpose eq366 eq66
    | exact resolve eq66 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq366
  have eq511 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  clear eq506
  have eq3740 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq511 (σ X0)
       have i₂ := eq348 X0
       grind)
    | exact superpose eq348 eq511
    | (have j1 := eq348 X0
       grind)
    | exact resolve eq511 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3753 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq348 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq3756 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3740 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq3740
    | (have j0 := eq3740 X0
       grind)
    | exact resolve eq3740 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3740
  have eq5700 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq78 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq78
    | (have j0 := eq78 x
       grind)
    | exact resolve eq78 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq5733 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq5700
    | exact resolve eq5700 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5700
  have eq5749 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5733
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq5733
    | exact resolve eq5733 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5733
  have eq5753 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq5749
    | exact resolve eq5749 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5749
  have eq18292 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq94 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18293 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq18292
    | exact resolve eq18292 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18292
  have eq18304 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq18293
       have r₂ := eq28
       grind)
    | exact resolve eq18293 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18293
  have eq18306 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq18304
    | exact resolve eq18304 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18304
  have eq18309 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18306 eq108
    | (have r₁ := eq108
       have r₂ := eq18306
       grind)
    | exact resolve eq108 eq18306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq18337 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18306 eq54
    | exact resolve eq54 eq18306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18342 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq18306
  have eq18344 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq18309
  have eq18345 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq206 eq18337
    | exact resolve eq18337 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18337
  have eq20784 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq18344
       have r₂ := eq18342
       grind)
    | exact resolve eq18344 eq18342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18344
  have eq20791 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20784 eq94
    | exact resolve eq94 eq20784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20784
  have eq20802 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq20791
  have eq20837 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq20802 eq54
    | exact resolve eq54 eq20802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20802
  have eq20890 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18345 eq20837
    | exact resolve eq20837 eq18345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18345 eq20837
  have eq20914 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq20890
  have eq20924 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq20914
       have r₂ := eq18342
       grind)
    | exact resolve eq20914 eq18342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18342 eq20914
  have eq20925 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq20924
       have r₂ := eq28
       grind)
    | exact resolve eq20924 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20924
  have eq20958 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20925 eq511
    | exact resolve eq511 eq20925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20925
  have eq21018 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq27 eq20958
    | exact resolve eq20958 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20958
  have eq21247 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21018 eq94
    | exact resolve eq94 eq21018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq21018
  have eq21257 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq21247
  have eq21260 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq21257
       have r₂ := eq28
       grind)
    | exact resolve eq21257 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21257
  have eq21263 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (k y x) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq107
       have i₂ := eq21260
       grind)
    | exact superpose eq21260 eq107
    | (have r₁ := eq107
       have r₂ := eq21260
       grind)
    | exact resolve eq107 eq21260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq21293 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq54 x x
       have i₂ := eq21260
       grind)
    | exact superpose eq21260 eq54
    | exact resolve eq54 eq21260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21302 : y ≠ (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq21260
  have eq21304 : y = (M.op x y) ∨ (k y x) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq21263
  have eq21305 : (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq205 eq21293
    | exact resolve eq21293 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq21293
  have eq21364 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq54 y x
       have i₂ := eq21305
       grind)
    | exact superpose eq21305 eq54
    | exact resolve eq54 eq21305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21379 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq21364
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq21364
    | exact resolve eq21364 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21364
  have eq21550 : (M.op y y) = (M.op (M.op x y) y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21379 eq51
    | exact resolve eq51 eq21379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq22391 : (M.op x y) = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21550 eq21379
    | exact resolve eq21379 eq21550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21379 eq21550
  have eq22413 : (M.op x y) = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq22391
  have eq22416 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq353
       have i₂ := eq22413
       grind)
    | exact superpose eq22413 eq353
    | exact resolve eq353 eq22413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353 eq22413
  have eq22466 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq22416
       have r₂ := eq21302
       grind)
    | exact resolve eq22416 eq21302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22416
  have eq22467 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq22466
    | exact resolve eq22466 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22466
  have eq22764 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq22467
       have i₂ := eq110 sF3
       grind)
    | exact superpose eq110 eq22467
    | (have j1 := eq110 (σ y)
       grind)
    | exact resolve eq22467 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq31661 : (k y x) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq21304
       have r₂ := eq21302
       grind)
    | exact resolve eq21304 eq21302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21302 eq21304
  have eq31663 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq31661
       grind)
    | exact superpose eq31661 eq73
    | exact resolve eq73 eq31661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31661
  have eq31943 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq31663
       have i₂ := eq21305
       grind)
    | exact superpose eq21305 eq31663
    | exact resolve eq31663 eq21305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21305 eq31663
  have eq32042 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq31943
  have eq32047 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq32042
    | exact resolve eq32042 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32042
  have eq32061 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32047 eq5753
    | exact resolve eq5753 eq32047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5753 eq32047
  have eq32070 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq32061
       have r₂ := eq28
       grind)
    | exact resolve eq32061 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32061
  have eq36742 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32070 eq54
    | exact resolve eq54 eq32070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32070
  have eq36758 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq206 eq36742
    | exact resolve eq36742 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq36742
  have eq37051 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq36758 eq54
    | exact resolve eq54 eq36758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq36758
  have eq37073 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq37051
    | exact resolve eq37051 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37051
  have eq37360 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq22764
  have eq37694 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq37073 eq52
    | exact resolve eq52 eq37073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq209735 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq37360 eq22467
    | exact resolve eq22467 eq37360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22467 eq37360
  have eq209800 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq209735
  have eq230143 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq37694 eq37073
    | exact resolve eq37073 eq37694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37073 eq37694
  have eq230193 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq230143
  have eq230215 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq230193 eq209800
    | exact resolve eq209800 eq230193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230193
  have eq230287 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq230215
  have eq230302 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq230287
       have r₂ := eq28
       grind)
    | exact resolve eq230287 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230287
  have eq230716 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq230302 eq207
    | exact resolve eq207 eq230302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230302
  have eq230746 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq230716
    | exact resolve eq230716 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230716
  have eq231672 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq230746 eq209800
    | exact resolve eq209800 eq230746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209800 eq230746
  have eq231744 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq231672
  have eq231758 : y = (M.op x x) := by
    first
    | (have r₁ := eq231744
       have r₂ := eq28
       grind)
    | exact resolve eq231744 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231744
  have eq231763 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq352
       have i₂ := eq231758
       grind)
    | exact superpose eq231758 eq352
    | exact resolve eq352 eq231758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq231769 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq511 x
       have i₂ := eq231758
       grind)
    | exact superpose eq231758 eq511
    | exact resolve eq511 eq231758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231796 : y ≠ y ∨ x = y ∨ y = (k x x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq231758
       grind)
    | exact superpose eq231758 eq12
    | exact resolve eq12 eq231758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231800 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq207 x x
       have i₂ := eq231758
       grind)
    | exact superpose eq231758 eq207
    | exact resolve eq207 eq231758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq231820 : y = (k x x) ∨ x = y := by grind
  clear eq231796
  have eq231828 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq231800
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq231800
    | exact resolve eq231800 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231800
  have eq231856 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq231769
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq231769
    | exact resolve eq231769 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq231769
  have eq231857 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq231763
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq231763
    | exact resolve eq231763 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231763
  have eq233239 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq231856
       grind)
    | exact superpose eq231856 eq73
    | exact resolve eq73 eq231856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233300 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21 eq233239
    | exact resolve eq233239 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233239
  have eq237909 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq3756 x
       have i₂ := eq231820
       grind)
    | exact superpose eq231820 eq3756
    | (have j0 := eq3756 x
       grind)
    | exact resolve eq3756 eq231820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3756 eq231820
  have eq237915 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq237909
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq237909
    | exact resolve eq237909 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq237909
  have eq237940 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq233300 eq237915
    | exact resolve eq237915 eq233300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237915
  have eq237951 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq237940
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq237940
    | exact resolve eq237940 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237940
  have eq237960 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq237951
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq237951
    | exact resolve eq237951 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237951
  have eq237963 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq27 eq237960
    | exact resolve eq237960 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237960
  have eq237964 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq237963
       have r₂ := eq28
       grind)
    | exact resolve eq237963 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237963
  have eq237965 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq237964
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq237964
    | exact resolve eq237964 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237964
  have eq239339 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq237965
  have eq249372 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq239339 eq231857
    | exact resolve eq231857 eq239339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231857 eq239339
  have eq249384 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq249372
  have eq249403 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq249384 eq511
    | exact resolve eq511 eq249384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511 eq249384
  have eq249494 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq233300 eq249403
    | exact resolve eq249403 eq233300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233300 eq249403
  have eq249508 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq249494
    | exact resolve eq249494 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249494
  have eq249513 : x = y := by
    first
    | (have r₁ := eq249508
       have r₂ := eq28
       grind)
    | exact resolve eq249508 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249508
  have eq249515 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq249513
       grind)
    | exact superpose eq249513 eq25
    | exact resolve eq25 eq249513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq249951 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq231828
       have i₂ := eq249513
       grind)
    | exact superpose eq249513 eq231828
    | exact resolve eq231828 eq249513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231828
  have eq249954 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq231856
       have i₂ := eq249513
       grind)
    | exact superpose eq249513 eq231856
    | exact resolve eq231856 eq249513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231856
  have eq249958 : y = (M.op x y) := by
    first
    | (have i₁ := eq249951
       have i₂ := eq231758
       grind)
    | exact superpose eq231758 eq249951
    | exact resolve eq249951 eq231758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231758 eq249951
  have eq250346 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq249515
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq249515
    | exact resolve eq249515 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249515
  have eq250349 : x = (M.op x y) := by
    first
    | (have i₁ := eq249958
       have i₂ := eq249513
       grind)
    | exact superpose eq249513 eq249958
    | exact resolve eq249958 eq249513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249513 eq249958
  have eq251647 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq250346 eq27
    | exact resolve eq27 eq250346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq250346
  have eq252010 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq250349 eq21
    | exact resolve eq21 eq250349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq252674 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq252010
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq252010
    | exact resolve eq252010 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252010
  have eq253159 : x = (k x x) := by
    first
    | exact superpose eq250349 eq249954
    | exact resolve eq249954 eq250349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249954 eq250349
  have eq253199 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3753 x
       have i₂ := eq253159
       grind)
    | exact superpose eq253159 eq3753
    | (have j0 := eq3753 x
       grind)
    | exact resolve eq3753 eq253159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3753 eq253159
  have eq253205 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq253199
  have eq253215 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq253205
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq253205
    | exact resolve eq253205 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq253205
  have eq253235 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq252674 eq253215
    | exact resolve eq253215 eq252674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253215
  have eq253335 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq252674 eq251647
    | exact resolve eq251647 eq252674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251647 eq252674
  have eq253430 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq253235 eq253335
    | exact resolve eq253335 eq253235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253235 eq253335
  have eq253431 : False := by grind
  exact eq253431

/-- `Equation4209`: `x ◇ y = ((z ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pxy_pyx_Equation4209 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4209 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4209.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X2 X1) X0) X1) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq21 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x X1)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq120 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (M.op (σ X0) (σ X1)) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X0) (σ X0)
       have i₂ := eq75 X0 X1
       grind)
    | (have i₁ := eq21 (σ X0) (σ X1)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq21
    | (have j1 := eq75 X0 X1
       grind)
    | exact resolve eq21 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq75 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq75 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq75 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq75 X1 X1
       grind)
    | exact resolve eq13 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq132 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq127 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq133 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq132 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq136 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq133 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq133
    | (have j0 := eq133 X0 X1
       grind)
    | exact resolve eq133 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq137 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq120 X0 X1
       have i₂ := eq21 (σ X0) (σ X1)
       grind)
    | exact superpose eq21 eq120
    | (have j0 := eq120 X0 X1
       grind)
    | exact resolve eq120 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq120
  have eq1177 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq136 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq136
    | exact resolve eq136 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq1217 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1177 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1177
    | (have j0 := eq1177 X0 X1
       grind)
    | exact resolve eq1177 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177
  have eq1219 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1217 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1217
    | (have j0 := eq1217 X0 X1
       grind)
    | exact resolve eq1217 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217
  have eq1446 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq137 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq137
    | exact resolve eq137 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq1486 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1446 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1446
    | (have j0 := eq1446 X0 X1
       grind)
    | exact resolve eq1446 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1446
  have eq13004 : ∀ X0 X1 : G, (M.op (σ X0) X1) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1219 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq13022 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq13004 X0 X1
       have j1 := eq1486 X1 X0
       grind)
    | (have r₁ := eq13004 X0 (σ X1)
       have r₂ := eq1486 (σ X0) X1
       grind)
    | (have r₁ := eq13004 X1 X0
       have r₂ := eq1486 X0 X1
       grind)
    | exact resolve eq13004 eq1486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486 eq13004
  have eq13041 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13022 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13022
    | exact resolve eq13022 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13082 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq13022 X1 (σ X0)
       grind)
    | exact superpose eq13022 eq15
    | (have j1 := eq13022 X1 (σ X0)
       grind)
    | exact resolve eq15 eq13022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13022
  have eq13245 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq13041 (τ X1) X0
       grind)
    | exact superpose eq13041 eq18
    | (have j1 := eq13041 (τ X1) X0
       grind)
    | exact resolve eq18 eq13041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq13041
  have eq14026 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13245 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13245
    | exact resolve eq13245 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13245
  have eq14146 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14026 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14026
    | (have j0 := eq14026 X0 X1
       grind)
    | exact resolve eq14026 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14026
  have eq14860 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13082 x y
       grind)
    | exact superpose eq13082 eq16
    | (have j1 := eq13082 x y
       grind)
    | exact resolve eq16 eq13082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13082
  have eq14977 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14860
       have i₂ := eq14146 y x
       grind)
    | exact superpose eq14146 eq14860
    | (have j1 := eq14146 (σ y) (σ x)
       grind)
    | (have r₁ := eq14860
       have r₂ := eq14146 y x
       grind)
    | exact resolve eq14860 eq14146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14980 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq14977
  have eq15076 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq14980
  have eq15214 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14860
       have i₂ := eq15076
       grind)
    | exact superpose eq15076 eq14860
    | exact resolve eq14860 eq15076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14860 eq15076
  have eq15215 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq15214
  have eq15216 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq15215
  have eq15262 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq15216
  have eq15328 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq15262
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq15262
    | exact resolve eq15262 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15262
  have eq15595 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15328
       grind)
    | exact superpose eq15328 eq16
    | exact resolve eq16 eq15328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15328
  have eq15845 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq15595
       have i₂ := eq14146 y x
       grind)
    | exact superpose eq14146 eq15595
    | (have j1 := eq14146 y x
       grind)
    | (have r₁ := eq15595
       have r₂ := eq14146 y x
       grind)
    | exact resolve eq15595 eq14146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14146
  have eq15848 : y = (M.op x x) := by grind
  clear eq15845
  have eq15861 : (M.op x y) = (k y x) := by grind
  clear eq15848
  have eq16316 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq15595
       have i₂ := eq15861
       grind)
    | exact superpose eq15861 eq15595
    | exact resolve eq15595 eq15861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15595 eq15861
  have eq16319 : False := by grind
  exact eq16319

/-- `Equation4209`: `x ◇ y = ((z ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyx_pxy_pyx_Equation4209 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4209 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4209.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X2 X1) X0) X1) := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq24 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x X1)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq41 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq41 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq55 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq55
    | (have j0 := eq55 (σ X0) (σ X1)
       grind)
    | exact resolve eq55 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq42 (τ X0)
       grind)
    | exact superpose eq42 eq18
    | exact resolve eq18 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq82 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81
    | exact resolve eq81 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq90 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq82
    | exact resolve eq82 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq82
  have eq94 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq90 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq114 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66 y x
       grind)
    | exact superpose eq66 eq16
    | (have j1 := eq66 y x
       grind)
    | exact resolve eq16 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq154 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq24 (σ X0) (σ X0)
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq24
    | exact resolve eq24 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq9
    | exact resolve eq9 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq114
       have i₂ := eq94 y
       grind)
    | exact superpose eq94 eq114
    | exact resolve eq114 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq404 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq403
       have i₂ := eq94 x
       grind)
    | exact superpose eq94 eq403
    | exact resolve eq403 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq403
  have eq432 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq404
       have i₂ := eq55 y x
       grind)
    | exact superpose eq55 eq404
    | (have j1 := eq55 x y
       grind)
    | exact resolve eq404 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq404
  have eq433 : (M.op y y) = (M.op x x) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq432
  have eq1494 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq154 y
       have i₂ := eq433
       grind)
    | exact superpose eq433 eq154
    | exact resolve eq154 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1506 : (M.op x x) = (M.op (M.op x x) y) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq24 y y
       have i₂ := eq433
       grind)
    | exact superpose eq433 eq24
    | exact resolve eq24 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq3592 : (M.op y x) = (M.op (M.op x x) x) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9 y x x
       have i₂ := eq1506
       grind)
    | exact superpose eq1506 eq9
    | exact resolve eq9 eq1506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3601 : (M.op x x) = (M.op y x) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3592
       have i₂ := eq24 x x
       grind)
    | exact superpose eq24 eq3592
    | exact resolve eq3592 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3592
  have eq3606 : (M.op x y) = (M.op (M.op x x) y) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq24 y x
       have i₂ := eq3601
       grind)
    | exact superpose eq3601 eq24
    | exact resolve eq24 eq3601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3601
  have eq5418 : (M.op x y) = (M.op x x) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1506
       have i₂ := eq3606
       grind)
    | exact superpose eq3606 eq1506
    | exact resolve eq1506 eq3606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506 eq3606
  have eq5427 : (M.op x y) = (M.op x x) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq5418
  have eq85771 : (M.op (σ y) (σ x)) = (M.op (σ (M.op x x)) (σ x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq155 x (σ y)
       have i₂ := eq1494
       grind)
    | exact superpose eq1494 eq155
    | exact resolve eq155 eq1494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85838 : (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq85771
       have i₂ := eq154 x
       grind)
    | exact superpose eq154 eq85771
    | exact resolve eq85771 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85771
  have eq86767 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x x)) (σ y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq24 (σ y) (σ x)
       have i₂ := eq85838
       grind)
    | exact superpose eq85838 eq24
    | exact resolve eq24 eq85838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85838
  have eq195781 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1494
       have i₂ := eq86767
       grind)
    | exact superpose eq86767 eq1494
    | exact resolve eq1494 eq86767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494 eq86767
  have eq195865 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq195781
  have eq197012 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq195865
       grind)
    | exact superpose eq195865 eq16
    | exact resolve eq16 eq195865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195865
  have eq197334 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq197012
       have i₂ := eq5427
       grind)
    | exact superpose eq5427 eq197012
    | exact resolve eq197012 eq5427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5427 eq197012
  have eq197335 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq197334
  have eq197336 : (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq197335
  have eq197338 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ y)) := by
    first
    | (have i₁ := eq154 y
       have i₂ := eq197336
       grind)
    | exact superpose eq197336 eq154
    | exact resolve eq154 eq197336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197363 : (M.op y y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq197336
       grind)
    | exact superpose eq197336 eq10
    | exact resolve eq10 eq197336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197336
  have eq198000 : (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq197363
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq197363
    | exact resolve eq197363 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197363
  have eq198155 : (M.op x x) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq24 y y
       have i₂ := eq198000
       grind)
    | exact superpose eq198000 eq24
    | exact resolve eq24 eq198000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198000
  have eq199476 : (M.op y x) = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq9 y x x
       have i₂ := eq198155
       grind)
    | exact superpose eq198155 eq9
    | exact resolve eq9 eq198155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199557 : (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq199476
       have i₂ := eq24 x x
       grind)
    | exact superpose eq24 eq199476
    | exact resolve eq199476 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199476
  have eq199585 : (M.op x y) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq24 y x
       have i₂ := eq199557
       grind)
    | exact superpose eq199557 eq24
    | exact resolve eq24 eq199557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199557
  have eq199637 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq199585
       have i₂ := eq198155
       grind)
    | exact superpose eq198155 eq199585
    | exact resolve eq199585 eq198155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198155 eq199585
  have eq203293 : (M.op (σ y) (σ x)) = (M.op (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq155 x (σ y)
       have i₂ := eq197338
       grind)
    | exact superpose eq197338 eq155
    | exact resolve eq155 eq197338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq203409 : (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq203293
       have i₂ := eq154 x
       grind)
    | exact superpose eq154 eq203293
    | exact resolve eq203293 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq203293
  have eq203566 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x x)) (σ y)) := by
    first
    | (have i₁ := eq24 (σ y) (σ x)
       have i₂ := eq203409
       grind)
    | exact superpose eq203409 eq24
    | exact resolve eq24 eq203409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq203409
  have eq203628 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq203566
       have i₂ := eq197338
       grind)
    | exact superpose eq197338 eq203566
    | exact resolve eq203566 eq197338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197338 eq203566
  have eq204260 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq203628
       grind)
    | exact superpose eq203628 eq16
    | exact resolve eq16 eq203628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203628
  have eq204396 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq204260
       have i₂ := eq199637
       grind)
    | exact superpose eq199637 eq204260
    | exact resolve eq204260 eq199637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199637 eq204260
  have eq204397 : False := by grind
  exact eq204397

/-- `Equation4209`: `x ◇ y = ((z ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pyy_pyx_Equation4209 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4209 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4209.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X2 X1) X0) X1) := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq24 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x X1)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq43 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq43 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq43 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq57 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq57
    | (have j0 := eq57 (σ X1) (σ X0)
       grind)
    | exact resolve eq57 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 X0
       have i₂ := eq57 (σ X1) X0
       grind)
    | exact superpose eq57 eq30
    | (have j1 := eq57 X0 (σ X1)
       grind)
    | exact resolve eq30 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq72 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq57 (τ X1) X0
       grind)
    | exact superpose eq57 eq17
    | (have j1 := eq57 X0 (τ X1)
       grind)
    | exact resolve eq17 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq82 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) X0
       have i₂ := eq44 (σ X0)
       grind)
    | exact superpose eq44 eq22
    | exact resolve eq22 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq83 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq44 (τ X0)
       grind)
    | exact superpose eq44 eq18
    | exact resolve eq18 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq84 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq83
    | exact resolve eq83 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq85 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq82
    | exact resolve eq82 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq92 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq84
    | exact resolve eq84 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq85
    | exact resolve eq85 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq96 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq92 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq92
    | exact resolve eq92 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq92 X0
       grind)
    | exact superpose eq92 eq10
    | exact resolve eq10 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq104 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op (M.op X0 X1) (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op (M.op X2 X1) X0) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op X1 X0) X1
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68 y x
       grind)
    | exact superpose eq68 eq16
    | (have j1 := eq68 y x
       grind)
    | exact resolve eq16 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X1) (σ X0)
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq24
    | (have j1 := eq68 X0 X1
       grind)
    | exact resolve eq24 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq24 (σ X0) (σ X0)
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq24
    | exact resolve eq24 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq24 (τ X0) (τ X0)
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq24
    | exact resolve eq24 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq9
    | exact resolve eq9 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq312 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (M.op (τ X1) (M.op (τ X1) X0)) ∨ (σ (M.op X0 (τ X1))) = (k X1 (σ (M.op (τ X1) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq72 (M.op (τ X1) X1) X1
       have i₂ := eq24 (τ X1) X1
       grind)
    | exact superpose eq24 eq72
    | exact resolve eq72 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq439 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq118
       have i₂ := eq57 y x
       grind)
    | exact superpose eq57 eq118
    | (have j1 := eq57 (σ x) (σ y)
       grind)
    | exact resolve eq118 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq118
  have eq440 : (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq439
  have eq473 : ∀ X0 X1 : G, (M.op X1 (τ (τ X0))) = (M.op (M.op (τ (τ (M.op X0 X0))) X1) (τ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq176 (τ X0) X1
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq176
    | exact resolve eq176 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq501 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X1 X0))) = (M.op (M.op X0 X1) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq105 (M.op X1 X0) X1
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq105
    | exact resolve eq105 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X1) X0) (M.op X0 X1)) = (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq105 X1 (M.op (M.op X2 X1) X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq105
    | exact resolve eq105 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq105 (σ X0) (σ X0)
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq105
    | exact resolve eq105 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq105 (τ X0) (τ X0)
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq105
    | exact resolve eq105 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq526 : ∀ X0 : G, (τ (M.op X0 (M.op X0 X0))) = (M.op (τ (M.op X0 (M.op X0 X0))) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq173 (M.op x x)
       have i₂ := eq105 x x
       grind)
    | exact superpose eq105 eq173
    | exact resolve eq173 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq519 X0
       have i₂ := eq103 (M.op X0 X0)
       grind)
    | exact superpose eq103 eq519
    | exact resolve eq519 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq543 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq517 X0
       have i₂ := eq96 (M.op X0 X0)
       grind)
    | exact superpose eq96 eq517
    | exact resolve eq517 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq550 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq541 X0
       have i₂ := eq105 X0 X0
       grind)
    | exact superpose eq105 eq541
    | exact resolve eq541 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq552 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq543 X0
       have i₂ := eq105 X0 X0
       grind)
    | exact superpose eq105 eq543
    | exact resolve eq543 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq567 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (M.op (τ (M.op X0 (M.op X0 X0))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq24 (τ X0) (τ (M.op X0 X0))
       have i₂ := eq550 X0
       grind)
    | exact superpose eq550 eq24
    | exact resolve eq24 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 (M.op X0 X0))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq567 X0
       have i₂ := eq173 X0
       grind)
    | exact superpose eq173 eq567
    | exact resolve eq567 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173 eq567
  have eq669 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq24 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq552 X0
       grind)
    | exact superpose eq552 eq24
    | exact resolve eq24 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq677 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq669 X0
       have i₂ := eq151 X0
       grind)
    | exact superpose eq151 eq669
    | exact resolve eq669 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq899 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = (M.op (M.op X0 X1) (M.op (M.op X2 X1) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104 (M.op X1 X0) X1 X2
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq104
    | exact resolve eq104 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq919 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) = (M.op (M.op X1 (σ X0)) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 (σ X0) (σ X0)
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq104
    | exact resolve eq104 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq1008 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq123 X0 X1
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq123
    | (have j0 := eq123 X0 X1
       have j1 := eq68 X0 X1
       grind)
    | (have r₁ := eq123 X1 X1
       have r₂ := eq68 X1 X1
       grind)
    | exact resolve eq123 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1013 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1008 X0 X1
       have j1 := eq123 X0 X1
       grind)
    | (have r₁ := eq1008 X1 X0
       have r₂ := eq123 X0 X1
       grind)
    | exact resolve eq1008 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1939 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq440
       grind)
    | exact superpose eq440 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq440
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq440
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq440
       grind)
    | exact resolve eq13 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1941 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq24 y x
       have i₂ := eq440
       grind)
    | exact superpose eq440 eq24
    | exact resolve eq24 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq1951 : (k y x) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq1939
  have eq1991 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (M.op (σ X1) (M.op (σ X1) X0)) ∨ (τ (M.op X0 (σ X1))) = (k X1 (τ (M.op (σ X1) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq71 (M.op (σ X1) X1) X1
       have i₂ := eq24 (σ X1) X1
       grind)
    | exact superpose eq24 eq71
    | exact resolve eq71 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq4561 : ∀ X0 : G, (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) = (M.op (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq526 (σ X0)
       have i₂ := eq93 X0
       grind)
    | exact superpose eq93 eq526
    | exact resolve eq526 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq4587 : ∀ X0 : G, (τ (M.op (σ X0) (σ (M.op X0 X0)))) = (M.op (τ (M.op (σ X0) (σ (M.op X0 X0)))) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4561 X0
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq4561
    | exact resolve eq4561 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4561
  have eq4597 : ∀ X0 : G, (τ (σ (M.op X0 (M.op X0 X0)))) = (M.op (τ (σ (M.op X0 (M.op X0 X0)))) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4587 X0
       have i₂ := eq552 X0
       grind)
    | exact superpose eq552 eq4587
    | exact resolve eq4587 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4587
  have eq4603 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4597 X0
       have i₂ := eq10 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq10 eq4597
    | exact resolve eq4597 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4597
  have eq5671 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 X1)) ∨ (σ (M.op X1 X0)) = (k (σ X0) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq312 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq312
    | exact resolve eq312 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq5736 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 X1)) ∨ (σ (M.op X1 X0)) = (σ (k X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5671 X0 X1
       have i₂ := eq15 X0 (M.op X0 X1)
       grind)
    | exact superpose eq15 eq5671
    | (have j0 := eq5671 X0 X1
       grind)
    | exact resolve eq5671 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5671
  have eq11828 : (M.op y y) = (M.op (M.op x y) y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq9 y y x
       have i₂ := eq1941
       grind)
    | exact superpose eq1941 eq9
    | exact resolve eq9 eq1941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14036 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op (M.op X0 X1) X1) ∨ (σ (M.op X0 X1)) = (σ (k X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (M.op X1 X0)
       have i₂ := eq5736 X1 X0
       grind)
    | exact superpose eq5736 eq24
    | (have j1 := eq5736 X1 X0
       grind)
    | exact resolve eq24 eq5736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5736
  have eq14097 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) ∨ (σ (M.op X0 X1)) = (σ (k X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14036 X0 X1
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq14036
    | (have j0 := eq14036 X0 X1
       grind)
    | exact resolve eq14036 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14036
  have eq20536 : (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1941
       have i₂ := eq11828
       grind)
    | exact superpose eq11828 eq1941
    | exact resolve eq1941 eq11828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1941 eq11828
  have eq20559 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq20536
  have eq20845 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ y)
       have i₂ := eq20559
       grind)
    | exact superpose eq20559 eq9
    | exact resolve eq9 eq20559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20848 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq24 (σ y) (σ x)
       have i₂ := eq20559
       grind)
    | exact superpose eq20559 eq24
    | exact resolve eq24 eq20559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22274 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) ∨ (σ (M.op X0 X1)) = (σ (k X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X0
       have i₂ := eq14097 X0 X1
       grind)
    | exact superpose eq14097 eq9
    | (have j1 := eq14097 X0 X1
       grind)
    | exact resolve eq9 eq14097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28142 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (σ (M.op X1 X0)) = (σ (k X0 (M.op X0 X1))) ∨ (σ (M.op X1 X0)) = (σ (k X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq14097 X1 X0
       have i₂ := eq22274 X1 X0
       grind)
    | exact superpose eq22274 eq14097
    | (have j0 := eq14097 X1 X0
       have j1 := eq22274 X1 X0
       grind)
    | exact resolve eq14097 eq22274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14097 eq22274
  have eq28189 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (σ (k X0 (M.op X0 X1))) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq28142 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28142
  have eq28799 : ∀ X0 X1 : G, (k X1 (M.op X1 X0)) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (M.op X1 X0))
       have i₂ := eq28189 X1 X0
       grind)
    | exact superpose eq28189 eq10
    | (have j1 := eq28189 X1 X0
       grind)
    | exact resolve eq10 eq28189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28189
  have eq28944 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28799 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq28799
    | (have j0 := eq28799 X0 X1
       grind)
    | exact resolve eq28799 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28799
  have eq29371 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) ∨ (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq28944 (M.op X0 X0) (M.op X0 (M.op X0 X0))
       have i₂ := eq4603 X0
       grind)
    | exact superpose eq4603 eq28944
    | (have j0 := eq28944 (M.op X0 X0) (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq28944 eq4603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28944
  have eq29692 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) ∨ (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq29371 X0
       have i₂ := eq44 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq44 eq29371
    | (have j0 := eq29371 X0
       grind)
    | exact resolve eq29371 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29371
  have eq29693 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq29692 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29692
  have eq29731 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq29693 X0
       have i₂ := eq501 X0 X0
       grind)
    | exact superpose eq501 eq29693
    | exact resolve eq29693 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29693
  have eq30280 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) = (M.op (M.op (σ X0) (σ (M.op X0 X0))) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq29731 (σ X0)
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq29731
    | exact resolve eq29731 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30281 : ∀ X0 : G, (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0)))) = (M.op (M.op (τ X0) (τ (M.op X0 X0))) (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq29731 (τ X0)
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq29731
    | exact resolve eq29731 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30288 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) (M.op X0 X0) X0
       have i₂ := eq29731 X0
       grind)
    | exact superpose eq29731 eq9
    | exact resolve eq9 eq29731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30350 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq30288 X0
       have i₂ := eq4603 X0
       grind)
    | exact superpose eq4603 eq30288
    | exact resolve eq30288 eq4603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30288
  have eq30354 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 (M.op X0 X0)))) = (M.op (τ (M.op X0 (M.op X0 X0))) (τ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq30281 X0
       have i₂ := eq550 X0
       grind)
    | exact superpose eq550 eq30281
    | exact resolve eq30281 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30281
  have eq30355 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq30280 X0
       have i₂ := eq552 X0
       grind)
    | exact superpose eq552 eq30280
    | exact resolve eq30280 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30280
  have eq30358 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 (M.op X0 X0)))) = (τ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq30354 X0
       have i₂ := eq103 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq103 eq30354
    | exact resolve eq30354 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30354
  have eq30359 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) = (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq30355 X0
       have i₂ := eq96 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq96 eq30355
    | exact resolve eq30355 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30355
  have eq30361 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 (M.op X0 X0)))) = (τ (M.op X0 (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq30358 X0
       have i₂ := eq29731 X0
       grind)
    | exact superpose eq29731 eq30358
    | exact resolve eq30358 eq29731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30358
  have eq30362 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) = (σ (M.op X0 (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq30359 X0
       have i₂ := eq29731 X0
       grind)
    | exact superpose eq29731 eq30359
    | exact resolve eq30359 eq29731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30359
  have eq30955 : ∀ X0 : G, (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ (M.op X0 X0))))) = (τ (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq30361 (τ X0)
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq30361
    | exact resolve eq30361 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30997 : ∀ X0 : G, (M.op (τ (M.op X0 (M.op X0 X0))) (τ X0)) = (M.op (τ (M.op X0 (M.op X0 (M.op X0 X0)))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq24 (τ X0) (τ (M.op X0 (M.op X0 X0)))
       have i₂ := eq30361 X0
       grind)
    | exact superpose eq30361 eq24
    | exact resolve eq24 eq30361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31031 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 (M.op X0 (M.op X0 X0)))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq30997 X0
       have i₂ := eq575 X0
       grind)
    | exact superpose eq575 eq30997
    | exact resolve eq30997 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30997
  have eq31068 : ∀ X0 : G, (M.op (τ (τ X0)) (τ (τ (M.op X0 (M.op X0 X0))))) = (τ (M.op (τ X0) (τ (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq30955 X0
       have i₂ := eq550 X0
       grind)
    | exact superpose eq550 eq30955
    | exact resolve eq30955 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30955
  have eq31123 : ∀ X0 : G, (M.op (τ (τ X0)) (τ (τ (M.op X0 (M.op X0 X0))))) = (τ (τ (M.op X0 (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq31068 X0
       have i₂ := eq30361 X0
       grind)
    | exact superpose eq30361 eq31068
    | exact resolve eq31068 eq30361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31068
  have eq31467 : ∀ X0 : G, (τ (τ (M.op X0 X0))) = (M.op (τ (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0))))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq31031 (τ X0)
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq31031
    | exact resolve eq31031 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31474 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (M.op (τ (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq31031 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31031
    | exact resolve eq31031 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31589 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (M.op (τ (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq31474 X0
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq31474
    | exact resolve eq31474 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31474
  have eq31593 : ∀ X0 : G, (τ (τ (M.op X0 X0))) = (M.op (τ (M.op (τ X0) (τ (M.op X0 (M.op X0 X0))))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq31467 X0
       have i₂ := eq550 X0
       grind)
    | exact superpose eq550 eq31467
    | exact resolve eq31467 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31467
  have eq31637 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (M.op (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq31589 X0
       have i₂ := eq552 X0
       grind)
    | exact superpose eq552 eq31589
    | exact resolve eq31589 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31589
  have eq31639 : ∀ X0 : G, (τ (τ (M.op X0 X0))) = (M.op (τ (τ (M.op X0 (M.op X0 (M.op X0 X0))))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq31593 X0
       have i₂ := eq30361 X0
       grind)
    | exact superpose eq30361 eq31593
    | exact resolve eq31593 eq30361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31593
  have eq31671 : ∀ X0 : G, (M.op X0 X0) = (M.op (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq31637 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq31637
    | exact resolve eq31637 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31637
  have eq42648 : ∀ X0 : G, (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))))) = (M.op (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) (σ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq919 X0 (σ (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq552 (M.op X0 X0)
       grind)
    | exact superpose eq552 eq919
    | exact resolve eq919 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq42700 : ∀ X0 : G, (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))))) = (M.op (M.op (σ (M.op X0 (M.op X0 X0))) (σ X0)) (σ (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq42648 x
       have i₂ := eq105 x x
       grind)
    | exact superpose eq105 eq42648
    | exact resolve eq42648 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42648
  have eq42739 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 (M.op X0 (M.op X0 X0))))) = (M.op (M.op (σ (M.op X0 (M.op X0 X0))) (σ X0)) (σ (M.op X0 (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq42700 x
       have i₂ := eq501 x x
       grind)
    | exact superpose eq501 eq42700
    | exact resolve eq42700 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42700
  have eq42757 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 (M.op X0 X0))))) = (M.op (σ X0) (σ (M.op X0 (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq42739 X0
       have i₂ := eq677 X0
       grind)
    | exact superpose eq677 eq42739
    | exact resolve eq42739 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677 eq42739
  have eq45554 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq513 (M.op X0 X0) (M.op X0 X0) X0
       have i₂ := eq4603 X0
       grind)
    | exact superpose eq4603 eq513
    | exact resolve eq513 eq4603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513 eq4603
  have eq45777 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq45554 x
       have i₂ := eq105 x x
       grind)
    | exact superpose eq105 eq45554
    | exact resolve eq45554 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45554
  have eq45792 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq45777 X0
       have i₂ := eq501 X0 X0
       grind)
    | exact superpose eq501 eq45777
    | exact resolve eq45777 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501 eq45777
  have eq45793 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq45792 X0
       have i₂ := eq29731 X0
       grind)
    | exact superpose eq29731 eq45792
    | exact resolve eq45792 eq29731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29731 eq45792
  have eq61870 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq9 (σ y) (σ y) (σ x)
       have i₂ := eq20848
       grind)
    | exact superpose eq20848 eq9
    | exact resolve eq9 eq20848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61930 : (σ (M.op y y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq61870
       have i₂ := eq96 y
       grind)
    | exact superpose eq96 eq61870
    | exact resolve eq61870 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61870
  have eq62257 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq20848
       have i₂ := eq61930
       grind)
    | exact superpose eq61930 eq20848
    | exact resolve eq20848 eq61930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20848 eq61930
  have eq62307 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq62257
  have eq65530 : ∀ X0 : G, (M.op (τ (τ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))))) (τ (τ X0))) = (M.op (τ (τ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq473 X0 (τ (τ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))))
       have i₂ := eq31123 (M.op X0 X0)
       grind)
    | exact superpose eq31123 eq473
    | exact resolve eq473 eq31123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31123
  have eq65676 : ∀ X0 : G, (M.op (τ (τ (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))))) (τ (τ X0))) = (M.op (τ (τ (M.op (M.op X0 X0) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq65530 x
       have i₂ := eq899 x x x
       grind)
    | exact superpose eq899 eq65530
    | exact resolve eq65530 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65530
  have eq65748 : ∀ X0 : G, (M.op (τ (τ (M.op X0 (M.op X0 (M.op X0 X0))))) (τ (τ X0))) = (M.op (τ (τ (M.op (M.op X0 X0) (M.op X0 (M.op X0 (M.op X0 X0)))))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq65676 x
       have i₂ := eq105 x x
       grind)
    | exact superpose eq105 eq65676
    | exact resolve eq65676 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65676
  have eq65812 : ∀ X0 : G, (τ (τ (M.op X0 X0))) = (M.op (τ (τ (M.op (M.op X0 X0) (M.op X0 (M.op X0 (M.op X0 X0)))))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq65748 X0
       have i₂ := eq31639 X0
       grind)
    | exact superpose eq31639 eq65748
    | exact resolve eq65748 eq31639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31639 eq65748
  have eq112468 : (M.op (σ x) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq20845 (σ x)
       have i₂ := eq24 (σ x) (σ y)
       grind)
    | exact superpose eq24 eq20845
    | exact resolve eq20845 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20845
  have eq112576 : (σ (M.op x x)) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq112468
       have i₂ := eq96 x
       grind)
    | exact superpose eq96 eq112468
    | exact resolve eq112468 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112468
  have eq113249 : (σ (M.op x x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq112576
       have i₂ := eq20559
       grind)
    | exact superpose eq20559 eq112576
    | exact resolve eq112576 eq20559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112576
  have eq113335 : (σ (M.op x x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq113249
  have eq113362 : (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq113335
       have i₂ := eq24 (σ x) (σ y)
       grind)
    | exact superpose eq24 eq113335
    | exact resolve eq113335 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113335
  have eq114084 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq20559
       have i₂ := eq113362
       grind)
    | exact superpose eq113362 eq20559
    | exact resolve eq20559 eq113362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20559 eq113362
  have eq114167 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq114084
  have eq114858 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq62307
       have i₂ := eq114167
       grind)
    | exact superpose eq114167 eq62307
    | exact resolve eq62307 eq114167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62307 eq114167
  have eq114944 : (M.op x y) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq114858
  have eq143703 : (M.op (σ y) (σ x)) = (M.op (σ (M.op x x)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq119 y x
       have i₂ := eq1951
       grind)
    | exact superpose eq1951 eq119
    | (have j0 := eq119 y x
       grind)
    | exact resolve eq119 eq1951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq143712 : (σ (k x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1013 x y
       have i₂ := eq1951
       grind)
    | exact superpose eq1951 eq1013
    | (have j0 := eq1013 y x
       grind)
    | exact resolve eq1013 eq1951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013 eq1951
  have eq143796 : (σ (k x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq143712
  have eq143804 : (M.op (σ y) (σ x)) = (M.op (σ (M.op x x)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq143703
  have eq143819 : (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq143804
       have i₂ := eq151 x
       grind)
    | exact superpose eq151 eq143804
    | exact resolve eq143804 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq143804
  have eq186043 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 X1)) ∨ (τ (M.op X1 X0)) = (k (τ X0) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1991 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1991
    | exact resolve eq1991 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1991
  have eq186529 : ∀ X0 X1 : G, (τ (M.op X1 X0)) = (τ (k X0 (M.op X0 X1))) ∨ (M.op X1 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq186043 X0 X1
       have i₂ := eq33 (M.op X0 X1) X0
       grind)
    | exact superpose eq33 eq186043
    | (have j0 := eq186043 X0 X1
       grind)
    | exact resolve eq186043 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq186043
  have eq187014 : ∀ X0 X1 : G, (k X1 (M.op X1 X0)) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 (M.op X1 X0))
       have i₂ := eq186529 X1 X0
       grind)
    | exact superpose eq186529 eq11
    | (have j1 := eq186529 X1 X0
       grind)
    | exact resolve eq11 eq186529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186529
  have eq187233 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X1) = (k X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq187014 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq187014
    | (have j0 := eq187014 X0 X1
       grind)
    | exact resolve eq187014 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187014
  have eq188580 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (M.op X1 X0)
       have i₂ := eq187233 X0 X1
       grind)
    | exact superpose eq187233 eq24
    | (have j1 := eq187233 X0 X1
       grind)
    | exact resolve eq24 eq187233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187233
  have eq188901 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq188580 X0 X1
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq188580
    | (have j0 := eq188580 X0 X1
       grind)
    | exact resolve eq188580 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188580
  have eq189926 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X1 (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq188901 (M.op X0 X1) X0
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq188901
    | (have j0 := eq188901 X0 X1
       grind)
    | exact resolve eq188901 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190200 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X0
       have i₂ := eq188901 X0 X1
       grind)
    | exact superpose eq188901 eq9
    | (have j1 := eq188901 X0 X1
       grind)
    | exact resolve eq9 eq188901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188901
  have eq191314 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X1 (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq190200 (M.op X0 X1) X0
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq190200
    | (have j0 := eq190200 X0 X1
       grind)
    | exact resolve eq190200 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190200
  have eq193020 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X1 (M.op X1 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq189926 (M.op X0 X1) X0
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq189926
    | (have j0 := eq189926 X0 X1
       grind)
    | exact resolve eq189926 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189926
  have eq194360 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X1 (M.op X1 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq191314 (M.op X0 X1) X0
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq191314
    | (have j0 := eq191314 X0 X1
       grind)
    | exact resolve eq191314 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191314
  have eq221553 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 (M.op X0 (M.op X0 (M.op X0 X1)))) ∨ (M.op X1 X0) = (k X0 (M.op X0 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq193020 X1 X0
       have i₂ := eq194360 X1 X0
       grind)
    | exact superpose eq194360 eq193020
    | (have j0 := eq193020 X1 X0
       have j1 := eq194360 X1 X0
       grind)
    | exact resolve eq193020 eq194360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193020 eq194360
  have eq221739 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X0 (M.op X0 (M.op X0 X1)))) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq221553 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221553
  have eq222429 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))))) = (k (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0))))) (M.op (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0))))) (M.op (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0))))) (M.op X0 X0)))) ∨ (M.op X0 (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))))) = (M.op (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0))))) (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))))) := by
    intro X0
    first
    | (have i₁ := eq221739 (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0))))) X0
       have i₂ := eq31671 X0
       grind)
    | exact superpose eq31671 eq221739
    | (have j0 := eq221739 (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0))))) X0
       grind)
    | exact resolve eq221739 eq31671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31671 eq221739
  have eq223150 : ∀ X0 : G, (M.op X0 (τ (σ (M.op X0 (M.op X0 (M.op X0 X0)))))) = (k (τ (σ (M.op X0 (M.op X0 (M.op X0 X0))))) (M.op (τ (σ (M.op X0 (M.op X0 (M.op X0 X0))))) (M.op (τ (σ (M.op X0 (M.op X0 (M.op X0 X0))))) (M.op X0 X0)))) ∨ (M.op X0 (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))))) = (M.op (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0))))) (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))))) := by
    intro X0
    first
    | (have i₁ := eq222429 X0
       have i₂ := eq30362 X0
       grind)
    | exact superpose eq30362 eq222429
    | (have j0 := eq222429 X0
       grind)
    | exact resolve eq222429 eq30362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222429
  have eq223347 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))) = (k (M.op X0 (M.op X0 (M.op X0 X0))) (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 X0)))) ∨ (M.op X0 (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))))) = (M.op (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0))))) (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))))) := by
    intro X0
    first
    | (have i₁ := eq223150 X0
       have i₂ := eq10 (M.op X0 (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq10 eq223150
    | (have j0 := eq223150 X0
       grind)
    | exact resolve eq223150 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223150
  have eq223442 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))) = (k (M.op X0 (M.op X0 (M.op X0 X0))) (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0)))) ∨ (M.op X0 (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))))) = (M.op (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0))))) (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))))) := by
    intro X0
    first
    | (have i₁ := eq223347 X0
       have i₂ := eq30350 X0
       grind)
    | exact superpose eq30350 eq223347
    | (have j0 := eq223347 X0
       grind)
    | exact resolve eq223347 eq30350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30350 eq223347
  have eq223485 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))) = (k (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 (M.op X0 X0)))) ∨ (M.op X0 (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))))) = (M.op (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0))))) (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))))) := by
    intro X0
    first
    | (have i₁ := eq223442 X0
       have i₂ := eq45793 X0
       grind)
    | exact superpose eq45793 eq223442
    | (have j0 := eq223442 X0
       grind)
    | exact resolve eq223442 eq45793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45793 eq223442
  have eq223512 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 (M.op X0 X0)))) ∨ (M.op X0 (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))))) = (M.op (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0))))) (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))))) := by
    intro X0
    first
    | (have i₁ := eq223485 X0
       have i₂ := eq44 (M.op X0 (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq44 eq223485
    | (have j0 := eq223485 X0
       grind)
    | exact resolve eq223485 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq223485
  have eq223529 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))))) = (τ (M.op (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))))) ∨ (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq223512 X0
       have i₂ := eq103 (M.op (σ X0) (σ (M.op X0 (M.op X0 X0))))
       grind)
    | exact superpose eq103 eq223512
    | (have j0 := eq223512 X0
       grind)
    | exact resolve eq223512 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223512
  have eq223545 : ∀ X0 : G, (M.op X0 (τ (σ (M.op X0 (M.op X0 (M.op X0 X0)))))) = (τ (M.op (σ (M.op X0 (M.op X0 (M.op X0 X0)))) (σ (M.op X0 (M.op X0 (M.op X0 X0)))))) ∨ (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq223529 X0
       have i₂ := eq30362 X0
       grind)
    | exact superpose eq30362 eq223529
    | (have j0 := eq223529 X0
       grind)
    | exact resolve eq223529 eq30362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223529
  have eq223560 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op X0 (τ (σ (M.op X0 (M.op X0 (M.op X0 X0)))))) ∨ (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq223545 X0
       have i₂ := eq93 (M.op X0 (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq93 eq223545
    | (have j0 := eq223545 X0
       grind)
    | exact resolve eq223545 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq223545
  have eq223570 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 (M.op X0 X0)))) ∨ (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq223560 X0
       have i₂ := eq10 (M.op X0 (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq10 eq223560
    | (have j0 := eq223560 X0
       grind)
    | exact resolve eq223560 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223560
  have eq223571 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq223570 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223570
  have eq263234 : ∀ X0 : G, (τ (τ (M.op (σ X0) (σ X0)))) = (M.op (τ (τ (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ X0))))))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq65812 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq65812
    | exact resolve eq65812 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263589 : ∀ X0 : G, (τ (τ (σ (M.op X0 X0)))) = (M.op (τ (τ (M.op (σ (M.op X0 X0)) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq263234 X0
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq263234
    | exact resolve eq263234 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263234
  have eq263742 : ∀ X0 : G, (τ (τ (σ (M.op X0 X0)))) = (M.op (τ (τ (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ (M.op X0 (M.op X0 X0))))))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq263589 X0
       have i₂ := eq552 X0
       grind)
    | exact superpose eq552 eq263589
    | exact resolve eq263589 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263589
  have eq263856 : ∀ X0 : G, (τ (τ (σ (M.op X0 X0)))) = (M.op (τ (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 (M.op X0 X0))))))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq263742 X0
       have i₂ := eq30362 X0
       grind)
    | exact superpose eq30362 eq263742
    | exact resolve eq263742 eq30362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263742
  have eq263935 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 (M.op X0 X0))))))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq263856 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq263856
    | exact resolve eq263856 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263856
  have eq1286763 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0)))))) = (M.op (σ (τ (M.op X0 X0))) (σ (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0)))))) := by
    intro X0
    first
    | (have i₁ := eq42757 (τ X0)
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq42757
    | exact resolve eq42757 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1286871 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 (M.op X0 X0))))))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq263935 X0
       have i₂ := eq42757 X0
       grind)
    | exact superpose eq42757 eq263935
    | exact resolve eq263935 eq42757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42757 eq263935
  have eq1287582 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (M.op (τ X0) (τ (M.op X0 (M.op X0 X0)))))) = (M.op (σ (τ (M.op X0 X0))) (σ (M.op (τ X0) (τ (M.op X0 (M.op X0 X0)))))) := by
    intro X0
    first
    | (have i₁ := eq1286763 X0
       have i₂ := eq550 X0
       grind)
    | exact superpose eq550 eq1286763
    | exact resolve eq1286763 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286763
  have eq1287876 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ (M.op X0 (M.op X0 (M.op X0 X0)))))) = (M.op (σ (τ (M.op X0 X0))) (σ (τ (M.op X0 (M.op X0 (M.op X0 X0)))))) := by
    intro X0
    first
    | (have i₁ := eq1287582 X0
       have i₂ := eq30361 X0
       grind)
    | exact superpose eq30361 eq1287582
    | exact resolve eq1287582 eq30361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287582
  have eq1288035 : ∀ X0 : G, (M.op (σ (τ (M.op X0 X0))) (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (σ (τ X0)) (M.op X0 (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1287876 X0
       have i₂ := eq11 (M.op X0 (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq11 eq1287876
    | exact resolve eq1287876 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287876
  have eq1288107 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (σ (τ (M.op X0 X0))) (M.op X0 (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1288035 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1288035
    | exact resolve eq1288035 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288035
  have eq1288146 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1288107 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq1288107
    | exact resolve eq1288107 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288107
  have eq1289736 : ∀ X0 : G, (τ (τ (M.op X0 X0))) = (M.op (τ (τ (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq65812 X0
       have i₂ := eq1288146 X0
       grind)
    | exact superpose eq1288146 eq65812
    | exact resolve eq65812 eq1288146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65812
  have eq1615839 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) = (M.op (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq223571 (σ X0)
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq223571
    | exact resolve eq223571 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1615840 : ∀ X0 : G, (M.op (τ X0) (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0))))) = (M.op (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0)))) (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq223571 (τ X0)
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq223571
    | exact resolve eq223571 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1616453 : ∀ X0 : G, (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 (M.op X0 X0))))) = (M.op (M.op (τ X0) (τ (M.op X0 (M.op X0 X0)))) (M.op (τ X0) (τ (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq1615840 X0
       have i₂ := eq550 X0
       grind)
    | exact superpose eq550 eq1615840
    | exact resolve eq1615840 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1615840
  have eq1616454 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 (M.op X0 X0))))) = (M.op (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) (M.op (σ X0) (σ (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq1615839 X0
       have i₂ := eq552 X0
       grind)
    | exact superpose eq552 eq1615839
    | exact resolve eq1615839 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1615839
  have eq1616482 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 (M.op X0 (M.op X0 X0))))) = (M.op (τ (M.op X0 (M.op X0 (M.op X0 X0)))) (τ (M.op X0 (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq1616453 X0
       have i₂ := eq30361 X0
       grind)
    | exact superpose eq30361 eq1616453
    | exact resolve eq1616453 eq30361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616453
  have eq1616483 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 (M.op X0 (M.op X0 X0))))) = (M.op (σ (M.op X0 (M.op X0 (M.op X0 X0)))) (σ (M.op X0 (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq1616454 X0
       have i₂ := eq30362 X0
       grind)
    | exact superpose eq30362 eq1616454
    | exact resolve eq1616454 eq30362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616454
  have eq1616504 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 (M.op X0 (M.op X0 X0))))) = (τ (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq1616482 X0
       have i₂ := eq103 (M.op X0 (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq103 eq1616482
    | exact resolve eq1616482 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616482
  have eq1616505 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 (M.op X0 (M.op X0 X0))))) = (σ (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq1616483 X0
       have i₂ := eq96 (M.op X0 (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq96 eq1616483
    | exact resolve eq1616483 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616483
  have eq1616518 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 (M.op X0 (M.op X0 X0))))) = (τ (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq1616504 X0
       have i₂ := eq223571 X0
       grind)
    | exact superpose eq223571 eq1616504
    | exact resolve eq1616504 eq223571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616504
  have eq1616519 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 (M.op X0 (M.op X0 X0))))) = (σ (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq1616505 X0
       have i₂ := eq223571 X0
       grind)
    | exact superpose eq223571 eq1616505
    | exact resolve eq1616505 eq223571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223571 eq1616505
  have eq1616963 : ∀ X0 : G, (M.op (τ (M.op (τ (M.op X0 X0)) (M.op (τ (M.op X0 X0)) (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))))) (τ (τ X0))) = (M.op (τ (M.op (τ (M.op X0 X0)) (M.op (τ (M.op X0 X0)) (M.op (τ (M.op X0 X0)) (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))))))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq473 X0 (τ (M.op (τ (M.op X0 X0)) (M.op (τ (M.op X0 X0)) (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))))))
       have i₂ := eq1616518 (τ (M.op X0 X0))
       grind)
    | exact superpose eq1616518 eq473
    | exact resolve eq473 eq1616518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq1617684 : ∀ X0 : G, (M.op (τ (M.op (τ (M.op X0 X0)) (M.op (τ (M.op X0 X0)) (τ (M.op (M.op X0 X0) (M.op X0 X0)))))) (τ (τ X0))) = (M.op (τ (M.op (τ (M.op X0 X0)) (M.op (τ (M.op X0 X0)) (M.op (τ (M.op X0 X0)) (τ (M.op (M.op X0 X0) (M.op X0 X0))))))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1616963 X0
       have i₂ := eq103 (M.op X0 X0)
       grind)
    | exact superpose eq103 eq1616963
    | exact resolve eq1616963 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq1616963
  have eq1618215 : ∀ X0 : G, (M.op (τ (M.op (τ (M.op X0 X0)) (τ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))))) (τ (τ X0))) = (M.op (τ (M.op (τ (M.op X0 X0)) (M.op (τ (M.op X0 X0)) (τ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))))))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1617684 X0
       have i₂ := eq550 (M.op X0 X0)
       grind)
    | exact superpose eq550 eq1617684
    | exact resolve eq1617684 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550 eq1617684
  have eq1618642 : ∀ X0 : G, (M.op (τ (τ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))))) (τ (τ X0))) = (M.op (τ (M.op (τ (M.op X0 X0)) (τ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))))))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1618215 X0
       have i₂ := eq30361 (M.op X0 X0)
       grind)
    | exact superpose eq30361 eq1618215
    | exact resolve eq1618215 eq30361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30361 eq1618215
  have eq1618956 : ∀ X0 : G, (M.op (τ (τ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))))) (τ (τ X0))) = (M.op (τ (τ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))))))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1618642 X0
       have i₂ := eq1616518 (M.op X0 X0)
       grind)
    | exact superpose eq1616518 eq1618642
    | exact resolve eq1618642 eq1616518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616518 eq1618642
  have eq1619123 : ∀ X0 : G, (M.op (τ (τ (M.op (M.op X0 X0) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))))) (τ (τ X0))) = (M.op (τ (τ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))))))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1618956 x
       have i₂ := eq899 x x x
       grind)
    | exact superpose eq899 eq1618956
    | exact resolve eq1618956 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899 eq1618956
  have eq1619181 : ∀ X0 : G, (M.op (τ (τ (M.op (M.op X0 X0) (M.op X0 (M.op X0 (M.op X0 X0)))))) (τ (τ X0))) = (M.op (τ (τ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 (M.op X0 (M.op X0 X0))))))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1619123 x
       have i₂ := eq105 x x
       grind)
    | exact superpose eq105 eq1619123
    | exact resolve eq1619123 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq1619123
  have eq1619212 : ∀ X0 : G, (M.op (τ (τ (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))))) (τ (τ X0))) = (M.op (τ (τ (M.op (M.op X0 X0) (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0))))))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1619181 X0
       have i₂ := eq1288146 X0
       grind)
    | exact superpose eq1288146 eq1619181
    | exact resolve eq1619181 eq1288146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288146 eq1619181
  have eq1619228 : ∀ X0 : G, (τ (τ (M.op X0 X0))) = (M.op (τ (τ (M.op (M.op X0 X0) (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0))))))) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1619212 X0
       have i₂ := eq1289736 X0
       grind)
    | exact superpose eq1289736 eq1619212
    | exact resolve eq1619212 eq1289736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289736 eq1619212
  have eq1742384 : ∀ X0 : G, (τ (τ (M.op (σ X0) (σ X0)))) = (M.op (τ (τ (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ X0)))))))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1619228 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1619228
    | exact resolve eq1619228 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619228
  have eq1743506 : ∀ X0 : G, (τ (τ (σ (M.op X0 X0)))) = (M.op (τ (τ (M.op (σ (M.op X0 X0)) (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))))))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1742384 X0
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq1742384
    | exact resolve eq1742384 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1742384
  have eq1744043 : ∀ X0 : G, (τ (τ (σ (M.op X0 X0)))) = (M.op (τ (τ (M.op (σ (M.op X0 X0)) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))))))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1743506 X0
       have i₂ := eq552 X0
       grind)
    | exact superpose eq552 eq1743506
    | exact resolve eq1743506 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq1743506
  have eq1744459 : ∀ X0 : G, (τ (τ (σ (M.op X0 X0)))) = (M.op (τ (τ (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ (M.op X0 (M.op X0 (M.op X0 X0)))))))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1744043 X0
       have i₂ := eq30362 X0
       grind)
    | exact superpose eq30362 eq1744043
    | exact resolve eq1744043 eq30362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30362 eq1744043
  have eq1744737 : ∀ X0 : G, (τ (τ (σ (M.op X0 X0)))) = (M.op (τ (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))))))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1744459 X0
       have i₂ := eq1616519 X0
       grind)
    | exact superpose eq1616519 eq1744459
    | exact resolve eq1744459 eq1616519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616519 eq1744459
  have eq1744873 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))))))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1744737 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1744737
    | exact resolve eq1744737 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1744737
  have eq2306374 : (σ (k x y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq143819
       have i₂ := eq68 x y
       grind)
    | exact superpose eq68 eq143819
    | (have j1 := eq68 y x
       grind)
    | exact resolve eq143819 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq143819
  have eq2307080 : (σ (k x y)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have j1 := eq123 y x
       grind)
    | (have r₁ := eq2306374
       have r₂ := eq123 y x
       grind)
    | exact resolve eq2306374 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq2306374
  have eq2307251 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq2307080
       have r₂ := eq143796
       grind)
    | exact resolve eq2307080 eq143796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143796 eq2307080
  have eq2307432 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24 (σ y) (σ x)
       have i₂ := eq2307251
       grind)
    | exact superpose eq2307251 eq24
    | exact resolve eq24 eq2307251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2307251
  have eq2309428 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 (σ y) (σ y) (σ x)
       have i₂ := eq2307432
       grind)
    | exact superpose eq2307432 eq9
    | exact resolve eq9 eq2307432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2309903 : (σ (M.op y y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2309428
       have i₂ := eq96 y
       grind)
    | exact superpose eq96 eq2309428
    | exact resolve eq2309428 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq2309428
  have eq2310024 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2307432
       have i₂ := eq2309903
       grind)
    | exact superpose eq2309903 eq2307432
    | exact resolve eq2307432 eq2309903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2307432 eq2309903
  have eq2310447 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x x) := by grind
  clear eq2310024
  have eq2312293 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2310447
       grind)
    | exact superpose eq2310447 eq16
    | exact resolve eq16 eq2310447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2310447
  have eq2313268 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2312293
       have i₂ := eq114944
       grind)
    | exact superpose eq114944 eq2312293
    | exact resolve eq2312293 eq114944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114944
  have eq2313325 : x = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq2313268
  have eq2314586 : (τ x) = (M.op (τ (M.op x (M.op x x))) (τ x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq31031 x
       have i₂ := eq2313325
       grind)
    | exact superpose eq2313325 eq31031
    | exact resolve eq31031 eq2313325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31031 eq2313325
  have eq2314973 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (τ (M.op x x)) = (τ x) := by
    first
    | (have i₁ := eq2314586
       have i₂ := eq575 x
       grind)
    | exact superpose eq575 eq2314586
    | exact resolve eq2314586 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq2314586
  have eq2327364 : (M.op y y) = (τ (σ (M.op x x))) ∨ (τ (M.op x x)) = (τ x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2314973
       grind)
    | exact superpose eq2314973 eq10
    | exact resolve eq10 eq2314973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2314973
  have eq2328418 : (M.op x x) = (M.op y y) ∨ (τ (M.op x x)) = (τ x) := by
    first
    | (have i₁ := eq2327364
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq2327364
    | exact resolve eq2327364 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2327364
  have eq2331539 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op (M.op x x) X0) y) ∨ (τ (M.op x x)) = (τ x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq2328418
       grind)
    | exact superpose eq2328418 eq9
    | exact resolve eq9 eq2328418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2331542 : (M.op x x) = (M.op (M.op x x) y) ∨ (τ (M.op x x)) = (τ x) := by
    first
    | (have i₁ := eq24 y y
       have i₂ := eq2328418
       grind)
    | exact superpose eq2328418 eq24
    | exact resolve eq24 eq2328418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2328418
  have eq2358755 : (M.op y x) = (M.op (M.op x x) x) ∨ (τ (M.op x x)) = (τ x) := by
    first
    | (have i₁ := eq9 y x x
       have i₂ := eq2331542
       grind)
    | exact superpose eq2331542 eq9
    | exact resolve eq9 eq2331542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2359148 : (M.op y x) = (M.op x x) ∨ (τ (M.op x x)) = (τ x) := by
    first
    | (have i₁ := eq2358755
       have i₂ := eq24 x x
       grind)
    | exact superpose eq24 eq2358755
    | exact resolve eq2358755 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2358755
  have eq2361328 : (M.op x y) = (M.op (M.op x x) y) ∨ (τ (M.op x x)) = (τ x) := by
    first
    | (have i₁ := eq24 y x
       have i₂ := eq2359148
       grind)
    | exact superpose eq2359148 eq24
    | exact resolve eq24 eq2359148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2359148
  have eq2408140 : (M.op y y) = (M.op (M.op x x) y) ∨ (τ (M.op x x)) = (τ x) ∨ (τ (M.op x x)) = (τ x) := by
    first
    | (have i₁ := eq2331539 y
       have i₂ := eq2331542
       grind)
    | exact superpose eq2331542 eq2331539
    | exact resolve eq2331539 eq2331542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2331539 eq2331542
  have eq2408600 : (M.op y y) = (M.op (M.op x x) y) ∨ (τ (M.op x x)) = (τ x) := by grind
  clear eq2408140
  have eq2411542 : (M.op x y) = (M.op y y) ∨ (τ (M.op x x)) = (τ x) ∨ (τ (M.op x x)) = (τ x) := by
    first
    | (have i₁ := eq2361328
       have i₂ := eq2408600
       grind)
    | exact superpose eq2408600 eq2361328
    | exact resolve eq2361328 eq2408600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2361328 eq2408600
  have eq2411830 : (M.op x y) = (M.op y y) ∨ (τ (M.op x x)) = (τ x) := by grind
  clear eq2411542
  have eq2414127 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ (τ (M.op x x)) = (τ x) := by
    first
    | (have i₁ := eq2312293
       have i₂ := eq2411830
       grind)
    | exact superpose eq2411830 eq2312293
    | exact resolve eq2312293 eq2411830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2312293 eq2411830
  have eq2414604 : x = (M.op x x) ∨ (τ (M.op x x)) = (τ x) := by grind
  clear eq2414127
  have eq2417609 : (τ x) = (M.op (τ (τ (M.op (σ x) (σ (M.op x (M.op x (M.op x x))))))) (τ x)) ∨ (τ (M.op x x)) = (τ x) := by
    first
    | (have i₁ := eq1744873 x
       have i₂ := eq2414604
       grind)
    | exact superpose eq2414604 eq1744873
    | exact resolve eq1744873 eq2414604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1744873 eq2414604
  have eq2417770 : (τ (M.op x x)) = (τ x) ∨ (τ (M.op x x)) = (τ x) := by
    first
    | (have i₁ := eq2417609
       have i₂ := eq1286871 x
       grind)
    | exact superpose eq1286871 eq2417609
    | exact resolve eq2417609 eq1286871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286871 eq2417609
  have eq2417771 : (τ (M.op x x)) = (τ x) := by grind
  clear eq2417770
  have eq2420016 : (M.op x x) = (σ (τ x)) := by
    first
    | (have i₁ := eq11 (M.op x x)
       have i₂ := eq2417771
       grind)
    | exact superpose eq2417771 eq11
    | exact resolve eq11 eq2417771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2417771
  have eq2421420 : x = (M.op x x) := by
    first
    | (have i₁ := eq2420016
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq2420016
    | exact resolve eq2420016 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2420016
  have eq2424568 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq2421420
       grind)
    | exact superpose eq2421420 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq2421420
       grind)
    | exact resolve eq12 eq2421420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2424571 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq155 x X0
       have i₂ := eq2421420
       grind)
    | exact superpose eq2421420 eq155
    | (have j0 := eq155 x X0
       grind)
    | exact resolve eq155 eq2421420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq2421420
  have eq2424967 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq2424571 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2424571
  have eq2424968 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq2424568 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2424568
  have eq2449182 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq2424967 (σ X0)
       grind)
    | exact superpose eq2424967 eq15
    | exact resolve eq15 eq2424967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2424967
  have eq2450257 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq2449182 X0
       have i₂ := eq2424968 X0
       grind)
    | exact superpose eq2424968 eq2449182
    | exact resolve eq2449182 eq2424968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2424968 eq2449182
  have eq2469689 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2450257 y
       grind)
    | exact superpose eq2450257 eq16
    | (have r₁ := eq16
       have r₂ := eq2450257 y
       grind)
    | exact resolve eq16 eq2450257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2450257
  have eq2470470 : False := by grind
  exact eq2470470

/-- `Equation4209`: `x ◇ y = ((z ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_pxx_pyx_Equation4209 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4209 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4209.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X2 X1) X0) X1) := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x X1)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X1 X0) X1
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq37 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X1 (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X1 X0)
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq13
    | (have j0 := eq13 X1 (M.op X1 X0)
       grind)
    | (have r₁ := eq13 X1 (M.op X1 X1)
       have r₂ := eq20 X1 X1
       grind)
    | exact resolve eq13 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq73 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = X0 := by
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
  have eq87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq22 X0 X0
       grind)
    | exact superpose eq22 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 (k X1 (τ X0)) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq71
    | exact resolve eq71 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq71 X0 X0
       grind)
    | exact superpose eq71 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq71 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq71 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq71 X0 X1
       grind)
    | exact resolve eq12 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq125 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq121 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq127 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq125 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq125 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq125 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq325 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq73
    | (have j0 := eq73 X1 X1
       grind)
    | exact resolve eq73 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq356 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq325 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq325
    | (have j0 := eq325 X1 X1
       grind)
    | exact resolve eq325 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq996 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = X0 ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq356 X2 X0
       grind)
    | exact superpose eq356 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq356 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq356 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq356 X0 X0
       grind)
    | exact resolve eq12 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1013 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq356 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq1014 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1013 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq1017 : ∀ X0 X1 X2 : G, (σ (k X2 X0)) = (σ (M.op X0 X2)) ∨ (M.op X0 X2) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq996 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq1032 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq1014 X0
       grind)
    | exact superpose eq1014 eq10
    | (have j1 := eq1014 X0
       grind)
    | exact resolve eq10 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1070 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1032 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1032
    | (have j0 := eq1032 X0
       grind)
    | exact resolve eq1032 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq1076 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1070 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq1070 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq1070 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070
  have eq1112 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq127 X0 X1
       have i₂ := eq1076 X0
       grind)
    | exact superpose eq1076 eq127
    | (have j0 := eq127 X0 X1
       grind)
    | exact resolve eq127 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq1128 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1076 (σ X0)
       grind)
    | exact superpose eq1076 eq15
    | exact resolve eq15 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1135 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0 X0
       have i₂ := eq1076 (τ X0)
       grind)
    | exact superpose eq1076 eq37
    | exact resolve eq37 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1145 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1135 X0
       have i₂ := eq1076 X0
       grind)
    | exact superpose eq1076 eq1135
    | exact resolve eq1135 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq1151 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1128 X0
       have i₂ := eq1076 X0
       grind)
    | exact superpose eq1076 eq1128
    | exact resolve eq1128 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076 eq1128
  have eq1212 : ∀ X0 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (k (τ X0) (τ (M.op X0 X0))) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq46 (τ X0) (τ X0)
       have i₂ := eq1145 X0
       grind)
    | exact superpose eq1145 eq46
    | exact resolve eq46 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq1221 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) (τ (M.op X0 X0))) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1212 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq1225 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k X0 (M.op X0 X0))) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1221 X0
       have i₂ := eq37 (M.op X0 X0) X0
       grind)
    | exact superpose eq37 eq1221
    | (have j0 := eq1221 X0
       grind)
    | exact resolve eq1221 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221
  have eq1235 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (τ (M.op X0 X0)) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1225 X0
       have i₂ := eq1145 (M.op X0 X0)
       grind)
    | exact superpose eq1145 eq1225
    | (have j0 := eq1225 X0
       grind)
    | exact resolve eq1225 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1241 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (M.op X0 (M.op X0 X0))) ∨ (τ (M.op X0 X0)) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1235 X0
       have i₂ := eq22 X0 X0
       grind)
    | exact superpose eq22 eq1235
    | (have j0 := eq1235 X0
       grind)
    | exact resolve eq1235 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1235
  have eq1298 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0) (σ X0)
       have i₂ := eq1151 X0
       grind)
    | exact superpose eq1151 eq20
    | exact resolve eq20 eq1151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1713 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (k (σ X0) X1) ∨ (k (σ X2) (k (σ X0) X1)) = (M.op (σ X2) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X2) (k (σ X0) X1)
       have i₂ := eq111 X0 X1 X2
       grind)
    | exact superpose eq111 eq13
    | (have j0 := eq13 (σ X2) (k (σ X0) X1)
       have j1 := eq111 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k (σ X0) X1)
       have r₂ := eq111 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (k (σ X0) X1)
       have r₂ := eq111 X0 X1 X2
       grind)
    | exact resolve eq13 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq1731 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (k (σ X0) X1) ∨ (k (σ X2) (k (σ X0) X1)) = (M.op (σ X2) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1713 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713
  have eq1732 : ∀ X0 X1 X2 : G, (k (σ X2) (k (σ X0) X1)) = (M.op (σ X2) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1731 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1731
  have eq1735 : ∀ X0 X1 X2 : G, (k (σ X2) (k (σ X0) X1)) = (σ (M.op X2 X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1732 X0 X1 X2
       have i₂ := eq1151 X2
       grind)
    | exact superpose eq1151 eq1732
    | (have j0 := eq1732 X0 X1 X2
       grind)
    | exact resolve eq1732 eq1151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1732
  have eq1751 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (σ (M.op X2 X2)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1735 X0 X1 X2
       have i₂ := eq32 X0 X1 X2
       grind)
    | exact superpose eq32 eq1735
    | (have j0 := eq1735 X0 X1 X2
       grind)
    | exact resolve eq1735 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1735
  have eq20178 : ∀ X0 X1 X2 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq1017 X0 X2 X1
       grind)
    | exact superpose eq1017 eq10
    | (have j1 := eq1017 X0 X2 X1
       grind)
    | exact resolve eq10 eq1017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017
  have eq20268 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20178 X0 X1 X2
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq20178
    | (have j0 := eq20178 X0 X1 X1
       grind)
    | exact resolve eq20178 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20178
  have eq20519 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq20268 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20268
  have eq20520 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq20519 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20519
  have eq20635 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 X0
       have i₂ := eq20520 (σ X1) X0
       grind)
    | exact superpose eq20520 eq34
    | (have j1 := eq20520 (σ X1) X0
       grind)
    | exact resolve eq34 eq20520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq20646 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq20520 (σ X1) (σ X0)
       grind)
    | exact superpose eq20520 eq15
    | (have j1 := eq20520 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq20520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20649 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq20520 (τ X1) X0
       grind)
    | exact superpose eq20520 eq17
    | (have j1 := eq20520 (τ X1) X0
       grind)
    | exact resolve eq17 eq20520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21148 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k X1 (τ (M.op (σ X1) X0))) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20635 (M.op (σ X1) X1) X1
       have i₂ := eq20 (σ X1) X1
       grind)
    | exact superpose eq20 eq20635
    | exact resolve eq20635 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20635
  have eq21794 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20649 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20649
    | exact resolve eq20649 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20649
  have eq21968 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21794 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq21794
    | (have j0 := eq21794 X0 X1
       grind)
    | exact resolve eq21794 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21794
  have eq23756 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20646 x y
       grind)
    | exact superpose eq20646 eq16
    | (have j1 := eq20646 x y
       grind)
    | exact resolve eq16 eq20646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20646
  have eq25414 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23756
       have i₂ := eq21968 y x
       grind)
    | exact superpose eq21968 eq23756
    | (have j1 := eq21968 (σ y) (σ x)
       grind)
    | (have r₁ := eq23756
       have r₂ := eq21968 y x
       grind)
    | exact resolve eq23756 eq21968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21968 eq23756
  have eq25417 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq25414
  have eq25423 : (M.op x x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20 x y
       have i₂ := eq25417
       grind)
    | exact superpose eq25417 eq20
    | exact resolve eq20 eq25417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57408 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) ∨ (σ (M.op X2 X2)) = (σ (k X2 (k (τ X0) (τ X1)))) ∨ (M.op (k X0 X1) (σ X2)) = (σ (k X2 (k (τ X0) (τ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1751 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1751
    | (have j0 := eq1751 (τ X0) X1 X2
       grind)
    | exact resolve eq1751 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751
  have eq57639 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (σ (k X2 (τ (k X0 X1)))) ∨ (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) ∨ (M.op (k X0 X1) (σ X2)) = (σ (k X2 (k (τ X0) (τ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57408 X0 X1 X2
       have i₂ := eq37 X1 X0
       grind)
    | exact superpose eq37 eq57408
    | (have j0 := eq57408 X0 X1 X2
       grind)
    | exact resolve eq57408 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57408
  have eq57688 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (k (σ X2) (k X0 X1)) ∨ (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) ∨ (M.op (k X0 X1) (σ X2)) = (σ (k X2 (k (τ X0) (τ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57639 X0 X1 X2
       have i₂ := eq18 (k X0 X1) X2
       grind)
    | exact superpose eq18 eq57639
    | (have j0 := eq57639 X0 X1 X2
       grind)
    | exact resolve eq57639 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57639
  have eq57727 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (σ X2)) = (σ (k X2 (τ (k X0 X1)))) ∨ (σ (M.op X2 X2)) = (k (σ X2) (k X0 X1)) ∨ (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57688 X0 X1 X2
       have i₂ := eq37 X1 X0
       grind)
    | exact superpose eq37 eq57688
    | (have j0 := eq57688 X0 X1 X2
       grind)
    | exact resolve eq57688 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq57688
  have eq57738 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (σ X2)) = (k (σ X2) (k X0 X1)) ∨ (σ (M.op X2 X2)) = (k (σ X2) (k X0 X1)) ∨ (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57727 X0 X1 X2
       have i₂ := eq18 (k X0 X1) X2
       grind)
    | exact superpose eq18 eq57727
    | (have j0 := eq57727 X0 X1 X2
       grind)
    | exact resolve eq57727 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq57727
  have eq57746 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (σ X2)) = (k (σ X2) (k X0 X1)) ∨ (σ (M.op X2 X2)) = (k (σ X2) (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq57738 X0 X1 X2
       have j1 := eq12 (σ X2) (k X0 X1)
       grind)
    | (have r₁ := eq57738 X0 X1 X2
       have r₂ := eq12 X0 (k X0 X1)
       grind)
    | exact resolve eq57738 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57738
  have eq67753 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (τ (M.op X0 X0))) ∨ (τ (M.op X0 X0)) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op X0 (M.op X0 X0))
       have i₂ := eq1241 X0
       grind)
    | exact superpose eq1241 eq11
    | (have j1 := eq1241 X0
       grind)
    | exact resolve eq11 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq67978 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq67753 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq67753
    | (have j0 := eq67753 X0
       grind)
    | exact resolve eq67753 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67753
  have eq68183 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) ∨ (τ (M.op X0 X0)) = (τ (k X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq67978 X0
       grind)
    | exact superpose eq67978 eq87
    | (have j0 := eq87 X0 X1
       have j1 := eq67978 X0
       grind)
    | (have r₁ := eq87 X0 X1
       have r₂ := eq67978 X0
       grind)
    | exact resolve eq87 eq67978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq67978
  have eq68291 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (k X0 (M.op X0 X0))) ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq68183 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68183
  have eq75593 : ∀ X0 X1 : G, (k X1 (σ (τ (M.op (σ (τ X1)) X0)))) = (σ (τ (M.op X0 (σ (τ X1))))) ∨ (M.op (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ (M.op (σ (τ X1)) X0))
       have i₂ := eq21148 X0 (τ X1)
       grind)
    | exact superpose eq21148 eq17
    | (have j1 := eq21148 X0 (τ X1)
       grind)
    | exact resolve eq17 eq21148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq21148
  have eq75725 : ∀ X0 X1 : G, (M.op X0 (σ (τ X1))) = (k X1 (σ (τ (M.op (σ (τ X1)) X0)))) ∨ (M.op (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq75593 X0 X1
       have i₂ := eq11 (M.op X0 (σ (τ X1)))
       grind)
    | exact superpose eq11 eq75593
    | (have j0 := eq75593 X0 X1
       grind)
    | exact resolve eq75593 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75593
  have eq75890 : ∀ X0 X1 : G, (M.op X0 (σ (τ X1))) = (k X1 (M.op (σ (τ X1)) X0)) ∨ (M.op (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq75725 X0 X1
       have i₂ := eq11 (M.op (σ (τ X1)) X0)
       grind)
    | exact superpose eq11 eq75725
    | (have j0 := eq75725 X0 X1
       grind)
    | exact resolve eq75725 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75725
  have eq76011 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op X1 X0)) ∨ (M.op (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq75890 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq75890
    | (have j0 := eq75890 X0 X1
       grind)
    | exact resolve eq75890 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75890
  have eq76091 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq76011 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq76011
    | (have j0 := eq76011 X0 X1
       grind)
    | exact resolve eq76011 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76011
  have eq76362 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (k y (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq76091 x y
       have i₂ := eq25423
       grind)
    | exact superpose eq25423 eq76091
    | exact resolve eq76091 eq25423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25423 eq76091
  have eq89081 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (σ (τ (M.op X0 X0))) ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 (M.op X0 X0))
       have i₂ := eq68291 X0 X1
       grind)
    | exact superpose eq68291 eq11
    | (have j1 := eq68291 X0 X1
       grind)
    | exact resolve eq11 eq68291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68291
  have eq89298 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq89081 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq89081
    | (have j0 := eq89081 X0 X1
       grind)
    | exact resolve eq89081 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89081
  have eq89650 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq89298 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89298
  have eq89683 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq89650 X0
       have j1 := eq20520 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq89650 X0
       have r₂ := eq20520 X0 (M.op X0 X0)
       grind)
    | exact resolve eq89650 eq20520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20520 eq89650
  have eq89783 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq89683 X0
       have i₂ := eq20 X0 X0
       grind)
    | exact superpose eq20 eq89683
    | exact resolve eq89683 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89683
  have eq165548 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (M.op (k X1 X2) X0) ∨ (k X0 (k X1 X2)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57746 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57746
    | exact resolve eq57746 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57746
  have eq165920 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (σ (τ (M.op X0 X0))) ∨ (k X0 (k X1 X2)) = (M.op (k X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq165548 X0 X1 X2
       have i₂ := eq1145 X0
       grind)
    | exact superpose eq1145 eq165548
    | (have j0 := eq165548 X0 X1 X2
       grind)
    | exact resolve eq165548 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145 eq165548
  have eq165965 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (M.op (k X1 X2) X0) ∨ (M.op X0 X0) = (k X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq165920 X0 X1 X2
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq165920
    | (have j0 := eq165920 X0 X1 X2
       grind)
    | exact resolve eq165920 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165920
  have eq166400 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (k X1 X2) X0) ∨ (M.op X0 X0) = (k X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq165965 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165965
  have eq166662 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq166400 X0 X0 (M.op X0 X0)
       have i₂ := eq89783 X0
       grind)
    | exact superpose eq89783 eq166400
    | exact resolve eq166400 eq89783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89783 eq166400
  have eq169021 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op (M.op X0 X1) X1) ∨ (M.op X1 X1) = (k X1 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq166662 (M.op X0 X1) X1
       have i₂ := eq9 (M.op X0 X1) X1 X0
       grind)
    | exact superpose eq9 eq166662
    | (have j0 := eq166662 (M.op X0 X1) X1
       grind)
    | exact resolve eq166662 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166662
  have eq230441 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq169021 (M.op X1 X0) X0
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq169021
    | (have j0 := eq169021 (M.op X1 X0) X0
       grind)
    | (have r₁ := eq169021 (M.op x X1) X1
       have r₂ := eq9 X1 X1 x
       grind)
    | exact resolve eq169021 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169021
  have eq230488 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0))) := by
    intro X0 X1
    first
    | (have j0 := eq230441 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230441
  have eq231477 : (M.op y y) = (k y (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq230488 y x
       have i₂ := eq25417
       grind)
    | exact superpose eq25417 eq230488
    | exact resolve eq230488 eq25417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230488
  have eq233512 : (M.op y y) = (k y (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq231477
       have i₂ := eq25417
       grind)
    | exact superpose eq25417 eq231477
    | exact resolve eq231477 eq25417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231477
  have eq233665 : (M.op y y) = (k y (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq233512
  have eq755628 : x = (M.op x x) ∨ x = (k y (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq76362
       have i₂ := eq25417
       grind)
    | exact superpose eq25417 eq76362
    | exact resolve eq76362 eq25417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25417 eq76362
  have eq755822 : x = (k y (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq755628
  have eq758591 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq233665
       have i₂ := eq755822
       grind)
    | exact superpose eq755822 eq233665
    | exact resolve eq233665 eq755822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233665 eq755822
  have eq758797 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq758591
  have eq758846 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ x)
       have i₂ := eq758797
       grind)
    | exact superpose eq758797 eq9
    | exact resolve eq9 eq758797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq773444 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq758846 (σ y)
       have i₂ := eq758797
       grind)
    | exact superpose eq758797 eq758846
    | exact resolve eq758846 eq758797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758846
  have eq773687 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq773444
  have eq773727 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq773687
       have i₂ := eq1151 y
       grind)
    | exact superpose eq1151 eq773687
    | exact resolve eq773687 eq1151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151 eq773687
  have eq776201 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq758797
       have i₂ := eq773727
       grind)
    | exact superpose eq773727 eq758797
    | exact resolve eq758797 eq773727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758797 eq773727
  have eq776427 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq776201
  have eq776710 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq776427
       grind)
    | exact superpose eq776427 eq10
    | exact resolve eq10 eq776427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776427
  have eq777178 : x = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq776710
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq776710
    | exact resolve eq776710 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776710
  have eq777179 : x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq777178
  have eq779966 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1298 y
       have i₂ := eq777179
       grind)
    | exact superpose eq777179 eq1298
    | exact resolve eq1298 eq777179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298
  have eq780211 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq20 y y
       have i₂ := eq777179
       grind)
    | exact superpose eq777179 eq20
    | exact resolve eq20 eq777179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq777179
  have eq794620 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq779966
       grind)
    | exact superpose eq779966 eq16
    | exact resolve eq16 eq779966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779966
  have eq794934 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq794620
       have i₂ := eq780211
       grind)
    | exact superpose eq780211 eq794620
    | exact resolve eq794620 eq780211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780211 eq794620
  have eq794945 : (σ x) ≠ (σ x) ∨ x = (M.op x x) := by grind
  clear eq794934
  have eq794946 : x = (M.op x x) := by grind
  clear eq794945
  have eq797705 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq794946
       grind)
    | exact superpose eq794946 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq794946
       grind)
    | exact resolve eq12 eq794946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq797711 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1112 x X0
       have i₂ := eq794946
       grind)
    | exact superpose eq794946 eq1112
    | (have j0 := eq1112 x X0
       grind)
    | exact resolve eq1112 eq794946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112 eq794946
  have eq798002 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq797711 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797711
  have eq798003 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq797705 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797705
  have eq810898 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq798002 (σ X0)
       grind)
    | exact superpose eq798002 eq15
    | exact resolve eq15 eq798002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798002
  have eq811655 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq810898 X0
       have i₂ := eq798003 X0
       grind)
    | exact superpose eq798003 eq810898
    | exact resolve eq810898 eq798003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798003 eq810898
  have eq827978 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq811655 y
       grind)
    | exact superpose eq811655 eq16
    | (have r₁ := eq16
       have r₂ := eq811655 y
       grind)
    | exact resolve eq16 eq811655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811655
  have eq828527 : False := by grind
  exact eq828527

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pxy_pxx_pxy_Equation422 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X2 X0)) X0 X0
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
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq81 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq85 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
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
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq85
    | (have j0 := eq85 X0
       grind)
    | exact resolve eq85 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq85
  have eq92 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq91 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | (have j0 := eq91 X0
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq93 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq92 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq92 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq92 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq96 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq93 (σ X0)
       grind)
    | exact superpose eq93 eq15
    | exact resolve eq15 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq96 X0
       have i₂ := eq93 X0
       grind)
    | exact superpose eq93 eq96
    | exact resolve eq96 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq96
  have eq127 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X3 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 (M.op X0 (M.op X1 (M.op X2 X0))) X1 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq21
    | exact resolve eq21 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq241 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
  have eq246 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq741 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq81
    | exact resolve eq81 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq784 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq741 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq741
    | (have j0 := eq741 X0 X1
       grind)
    | exact resolve eq741 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq879 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq246 (τ X0) (τ X1)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq246
    | (have j0 := eq246 (τ X0) (τ X1)
       grind)
    | exact resolve eq246 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq887 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq879 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq879
    | (have j0 := eq879 X0 X1
       grind)
    | exact resolve eq879 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq890 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq887 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq887
    | (have j0 := eq887 X0 X1
       grind)
    | exact resolve eq887 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq892 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq890 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq890
    | (have j0 := eq890 X0 X1
       grind)
    | exact resolve eq890 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq893 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq892 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq892
    | (have j0 := eq892 X0 X1
       grind)
    | exact resolve eq892 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq894 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq893 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq893
    | (have j0 := eq893 X0 X1
       grind)
    | exact resolve eq893 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq895 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq894 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq894
    | (have j0 := eq894 X0 X1
       grind)
    | exact resolve eq894 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq1070 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq241
       have i₂ := eq784 x y
       grind)
    | exact superpose eq784 eq241
    | (have j1 := eq784 (σ x) (σ y)
       grind)
    | (have r₁ := eq241
       have r₂ := eq784 x y
       grind)
    | (have r₁ := eq241
       have r₂ := eq784 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq241
       have r₂ := eq784 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq241 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq784
  have eq1071 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq1070
  have eq8045 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1071
       grind)
    | exact superpose eq1071 eq16
    | exact resolve eq16 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071
  have eq8046 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8045
       have r₂ := eq107 x
       grind)
    | exact resolve eq8045 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8045
  have eq8162 : y ≠ y ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq8046
       grind)
    | exact superpose eq8046 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq8046
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq8046
       grind)
    | exact resolve eq12 eq8046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8046
  have eq8185 : y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8162
  have eq8197 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq246 x y
       have i₂ := eq8185
       grind)
    | exact superpose eq8185 eq246
    | (have j0 := eq246 x y
       grind)
    | exact resolve eq246 eq8185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq8185
  have eq8211 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8197
  have eq8212 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq8211
  have eq8352 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8212
       grind)
    | exact superpose eq8212 eq16
    | exact resolve eq16 eq8212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8354 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq8212
       grind)
    | exact superpose eq8212 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq8212
       grind)
    | exact resolve eq12 eq8212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8212
  have eq8378 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq8354
  have eq8383 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq8378
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq8378
    | exact resolve eq8378 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8378
  have eq8505 : y = (τ (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8383
       grind)
    | exact superpose eq8383 eq10
    | exact resolve eq10 eq8383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8383
  have eq8572 : x = y ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq8505
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8505
    | exact resolve eq8505 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8505
  have eq8580 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8572
       grind)
    | exact superpose eq8572 eq16
    | exact resolve eq16 eq8572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8572
  have eq8581 : (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq8580
       have r₂ := eq107 x
       grind)
    | exact resolve eq8580 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8580
  have eq8757 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq8581
       grind)
    | exact superpose eq8581 eq10
    | exact resolve eq10 eq8581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8581
  have eq8825 : y = (k x y) := by
    first
    | (have i₁ := eq8757
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq8757
    | exact resolve eq8757 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8757
  have eq8845 : y ≠ y ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq895 x y
       have i₂ := eq8825
       grind)
    | exact superpose eq8825 eq895
    | (have j0 := eq895 x y
       grind)
    | (have r₁ := eq895 x y
       have r₂ := eq8825
       grind)
    | exact resolve eq895 eq8825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895 eq8825
  have eq8852 : x = y ∨ y = (M.op x y) := by grind
  clear eq8845
  have eq9036 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8852
       grind)
    | exact superpose eq8852 eq16
    | exact resolve eq16 eq8852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8852
  have eq9041 : y = (M.op x y) := by
    first
    | (have r₁ := eq9036
       have r₂ := eq107 x
       grind)
    | exact resolve eq9036 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9036
  have eq9045 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8352
       have i₂ := eq9041
       grind)
    | exact superpose eq9041 eq8352
    | exact resolve eq8352 eq9041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8352
  have eq9053 : ∀ X0 X1 : G, y = (M.op y (M.op y (M.op y (M.op X0 (M.op X1 y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq127 y x x x
       have i₂ := eq9041
       grind)
    | exact superpose eq9041 eq127
    | exact resolve eq127 eq9041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq9078 : (σ x) = (σ y) := by grind
  clear eq9045
  have eq9081 : y = (M.op y y) := by
    first
    | (have i₁ := eq9053 x x
       have i₂ := eq9 y x x
       grind)
    | exact superpose eq9 eq9053
    | exact resolve eq9053 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9053
  have eq9185 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9078
       grind)
    | exact superpose eq9078 eq16
    | exact resolve eq16 eq9078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9212 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq107 y
       have i₂ := eq9078
       grind)
    | exact superpose eq9078 eq107
    | exact resolve eq107 eq9078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9235 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9212
       have i₂ := eq9081
       grind)
    | exact superpose eq9081 eq9212
    | exact resolve eq9212 eq9081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9081 eq9212
  have eq9258 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9185
       have i₂ := eq107 x
       grind)
    | exact superpose eq107 eq9185
    | exact resolve eq9185 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9185
  have eq9262 : (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9235
       have i₂ := eq107 x
       grind)
    | exact superpose eq107 eq9235
    | exact resolve eq9235 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq9235
  have eq9268 : (σ y) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9258
       have i₂ := eq9041
       grind)
    | exact superpose eq9041 eq9258
    | exact resolve eq9258 eq9041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9041 eq9258
  have eq9270 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9262
       have i₂ := eq9078
       grind)
    | exact superpose eq9078 eq9262
    | exact resolve eq9262 eq9078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9262
  have eq9274 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9268
       have i₂ := eq9078
       grind)
    | exact superpose eq9078 eq9268
    | exact resolve eq9268 eq9078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9078 eq9268
  have eq9278 : False := by grind
  exact eq9278

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation422 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq66 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq76 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq67 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq77 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq76 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq92 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq77 (σ X0)
       grind)
    | exact superpose eq77 eq15
    | exact resolve eq15 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq92 X0
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq92
    | exact resolve eq92 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq92
  have eq120 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq103 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq103
    | (have j1 := eq14 (σ X0) (σ (M.op X0 X0))
       grind)
    | exact resolve eq103 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq134 X0 X1
       have j1 := eq120 X0 X1
       grind)
    | (have r₁ := eq134 X0 X1
       have r₂ := eq120 X0 X1
       grind)
    | (have r₁ := eq134 X0 (σ (M.op X0 X0))
       have r₂ := eq120 X0 X1
       grind)
    | (have r₁ := eq134 (M.op X0 X0) (σ X0)
       have r₂ := eq120 X0 X1
       grind)
    | exact resolve eq134 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq134
  have eq166 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq144 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq144
    | exact resolve eq144 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq144 X0 (σ X1)
       grind)
    | exact superpose eq144 eq15
    | (have j1 := eq144 (k X1 X0) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq178 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq166 (τ X0) X1
       grind)
    | exact superpose eq166 eq19
    | (have j1 := eq166 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq166
  have eq264 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq178 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq178
    | exact resolve eq178 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq289 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq264 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq264
    | (have j0 := eq264 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq264 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq897 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq171 x y
       grind)
    | exact superpose eq171 eq16
    | (have j1 := eq171 x y
       grind)
    | exact resolve eq16 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq911 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq897
       have i₂ := eq289 x y
       grind)
    | exact superpose eq289 eq897
    | (have j1 := eq289 (σ x) (σ y)
       grind)
    | (have r₁ := eq897
       have r₂ := eq289 x y
       grind)
    | (have r₁ := eq897
       have r₂ := eq289 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq897
       have r₂ := eq289 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq897 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq897
  have eq912 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq911
  have eq914 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq912
       grind)
    | exact superpose eq912 eq16
    | exact resolve eq16 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq915 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq914
       have r₂ := eq103 x
       grind)
    | exact resolve eq914 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq916 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq915
       grind)
    | exact superpose eq915 eq16
    | exact resolve eq16 eq915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq917 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq915
       grind)
    | exact superpose eq915 eq10
    | exact resolve eq10 eq915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq959 : x = y := by
    first
    | (have i₁ := eq917
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq917
    | exact resolve eq917 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq960 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq916
       have i₂ := eq103 x
       grind)
    | exact superpose eq103 eq916
    | exact resolve eq916 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq916
  have eq961 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq960
       have i₂ := eq959
       grind)
    | exact superpose eq959 eq960
    | exact resolve eq960 eq959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959 eq960
  have eq962 : False := by grind
  exact eq962
