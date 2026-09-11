import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation630 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law630 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  clear eq18
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
  have eq149 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq150 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq715 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (τ X1)
       have i₂ := eq149 X1 X0
       grind)
    | exact superpose eq149 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq149 X1 X0
       grind)
    | (have r₁ := eq13 X1 (τ X0)
       have r₂ := eq149 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq149 X0 (M.op X1 (τ X0))
       grind)
    | exact resolve eq13 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq716 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq715 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq717 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (k X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq716 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq776 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq150 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq2264 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq717 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq717
    | exact resolve eq717 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq2318 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2264 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2264
    | (have j0 := eq2264 X0 X1
       grind)
    | exact resolve eq2264 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2264
  have eq2363 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq2318 X0 X1
       grind)
    | exact superpose eq2318 eq10
    | (have j1 := eq2318 X0 X1
       grind)
    | exact resolve eq10 eq2318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2406 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2363 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2363
    | (have j0 := eq2363 X0 X1
       grind)
    | exact resolve eq2363 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2363
  have eq2421 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq2406 (σ X0) X1
       grind)
    | exact superpose eq2406 eq28
    | (have j1 := eq2406 (σ X0) X1
       grind)
    | exact resolve eq28 eq2406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2406
  have eq4286 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq2421 X1 (σ X0)
       grind)
    | exact superpose eq2421 eq37
    | (have j1 := eq2421 X1 (σ X0)
       grind)
    | exact resolve eq37 eq2421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2421
  have eq4351 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4286 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4286
    | (have j0 := eq4286 X0 X1
       grind)
    | exact resolve eq4286 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4286
  have eq4383 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4351 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4351
    | (have j0 := eq4351 X0 X1
       grind)
    | exact resolve eq4351 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4351
  have eq4393 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4383 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4383
    | (have j0 := eq4383 X0 X1
       grind)
    | exact resolve eq4383 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4383
  have eq4596 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq4393 X0 X1
       grind)
    | exact superpose eq4393 eq11
    | (have j1 := eq4393 X0 X1
       grind)
    | exact resolve eq11 eq4393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4393
  have eq5472 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4596 y x
       grind)
    | exact superpose eq4596 eq16
    | (have j1 := eq4596 y x
       grind)
    | exact resolve eq16 eq4596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4596
  have eq5498 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5472
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq5472
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq5472
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5472
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5472 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5499 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq5472
       have i₂ := eq2318 x y
       grind)
    | exact superpose eq2318 eq5472
    | (have j1 := eq2318 x y
       grind)
    | (have r₁ := eq5472
       have r₂ := eq2318 x y
       grind)
    | (have r₁ := eq5472
       have r₂ := eq2318 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5472
       have r₂ := eq2318 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5472 eq2318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2318 eq5472
  have eq5502 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5499
  have eq5503 : x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by grind
  clear eq5502
  have eq5504 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5498
  have eq5505 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5504
  have eq5509 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5503
       grind)
    | exact superpose eq5503 eq16
    | exact resolve eq16 eq5503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5503
  have eq5510 : y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5509
       have r₂ := eq22 x
       grind)
    | exact resolve eq5509 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5509
  have eq5515 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq776 x y
       have i₂ := eq5510
       grind)
    | exact superpose eq5510 eq776
    | (have j0 := eq776 x y
       grind)
    | exact resolve eq776 eq5510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776 eq5510
  have eq5521 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5515
  have eq5522 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5521
  have eq5534 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5522
       grind)
    | exact superpose eq5522 eq16
    | exact resolve eq16 eq5522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5522
  have eq5550 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5534
       have i₂ := eq5505
       grind)
    | exact superpose eq5505 eq5534
    | exact resolve eq5534 eq5505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5505 eq5534
  have eq5551 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5550
  have eq5552 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq5551
  have eq5553 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5552
       grind)
    | exact superpose eq5552 eq16
    | exact resolve eq16 eq5552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5552
  have eq5554 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq5553
       have r₂ := eq22 x
       grind)
    | exact resolve eq5553 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5553
  have eq5555 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5554
       grind)
    | exact superpose eq5554 eq16
    | exact resolve eq16 eq5554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5556 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5554
       grind)
    | exact superpose eq5554 eq10
    | exact resolve eq10 eq5554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5554
  have eq5610 : x = y := by
    first
    | (have i₁ := eq5556
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5556
    | exact resolve eq5556 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5556
  have eq5611 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5555
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5555
    | exact resolve eq5555 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5555
  have eq5612 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5611
       have i₂ := eq5610
       grind)
    | exact superpose eq5610 eq5611
    | exact resolve eq5611 eq5610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5610 eq5611
  have eq5613 : False := by grind
  exact eq5613

/-- `Equation633`: `x = x ◇ (y ◇ ((x ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation633 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law633 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law633.models_iff G M).mp hM
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  clear eq18
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
  have eq125 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq126 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq833 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq126 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq3854 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq125 X0 X1
       grind)
    | exact superpose eq125 eq13
    | (have j0 := eq13 (τ X0) X1
       have j1 := eq125 X0 X1
       grind)
    | (have r₁ := eq13 X1 (τ X0)
       have r₂ := eq125 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X0)
       have r₂ := eq125 X0 (M.op (τ X0) X0)
       grind)
    | exact resolve eq13 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq3866 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3854 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3854
  have eq3867 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (k X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3866 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3866
  have eq4007 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3867 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3867
    | exact resolve eq3867 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3867
  have eq4072 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4007 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4007
    | (have j0 := eq4007 X0 X1
       grind)
    | exact resolve eq4007 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4007
  have eq4130 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq4072 X0 X1
       grind)
    | exact superpose eq4072 eq10
    | (have j1 := eq4072 X0 X1
       grind)
    | exact resolve eq10 eq4072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4178 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4130 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq4130
    | (have j0 := eq4130 X0 X1
       grind)
    | exact resolve eq4130 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4130
  have eq4236 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq4178 X0 (σ X1)
       grind)
    | exact superpose eq4178 eq37
    | (have j1 := eq4178 X0 (σ X1)
       grind)
    | exact resolve eq37 eq4178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq4178
  have eq4504 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) X0
       have i₂ := eq4236 (σ X0) X1
       grind)
    | exact superpose eq4236 eq28
    | (have j1 := eq4236 (σ X0) X1
       grind)
    | exact resolve eq28 eq4236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4236
  have eq4566 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4504 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4504
    | (have j0 := eq4504 X0 X1
       grind)
    | exact resolve eq4504 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4504
  have eq4601 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4566 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4566
    | (have j0 := eq4566 X0 X1
       grind)
    | exact resolve eq4566 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4566
  have eq4611 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4601 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4601
    | (have j0 := eq4601 X0 X1
       grind)
    | exact resolve eq4601 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4601
  have eq4818 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq4611 X1 X0
       grind)
    | exact superpose eq4611 eq11
    | (have j1 := eq4611 X1 X0
       grind)
    | exact resolve eq11 eq4611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4611
  have eq5737 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4818 y x
       grind)
    | exact superpose eq4818 eq16
    | (have j1 := eq4818 y x
       grind)
    | exact resolve eq16 eq4818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4818
  have eq5771 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5737
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq5737
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq5737
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5737
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5737 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5772 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq5737
       have i₂ := eq4072 x y
       grind)
    | exact superpose eq4072 eq5737
    | (have j1 := eq4072 x y
       grind)
    | (have r₁ := eq5737
       have r₂ := eq4072 x y
       grind)
    | (have r₁ := eq5737
       have r₂ := eq4072 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5737
       have r₂ := eq4072 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5737 eq4072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4072 eq5737
  have eq5775 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5772
  have eq5776 : x = y ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq5775
  have eq5777 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5771
  have eq5778 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq5777
  have eq5782 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5776
       grind)
    | exact superpose eq5776 eq16
    | exact resolve eq16 eq5776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5776
  have eq5783 : x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5782
       have r₂ := eq22 x
       grind)
    | exact resolve eq5782 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5782
  have eq5787 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq833 x y
       have i₂ := eq5783
       grind)
    | exact superpose eq5783 eq833
    | (have j0 := eq833 x y
       grind)
    | exact resolve eq833 eq5783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833 eq5783
  have eq5794 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5787
  have eq5795 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5794
  have eq5799 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5778
       grind)
    | exact superpose eq5778 eq16
    | exact resolve eq16 eq5778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5778
  have eq5800 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5799
       have r₂ := eq22 x
       grind)
    | exact resolve eq5799 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5799
  have eq5813 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5795
       grind)
    | exact superpose eq5795 eq16
    | exact resolve eq16 eq5795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5795
  have eq5836 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5813
       have i₂ := eq5800
       grind)
    | exact superpose eq5800 eq5813
    | exact resolve eq5813 eq5800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5800 eq5813
  have eq5837 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq5836
  have eq5838 : (σ x) = (σ y) := by grind
  clear eq5837
  have eq5839 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5838
       grind)
    | exact superpose eq5838 eq16
    | exact resolve eq16 eq5838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5840 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5838
       grind)
    | exact superpose eq5838 eq10
    | exact resolve eq10 eq5838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5838
  have eq5894 : x = y := by
    first
    | (have i₁ := eq5840
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5840
    | exact resolve eq5840 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5840
  have eq5895 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5839
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5839
    | exact resolve eq5839 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5839
  have eq5896 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5895
       have i₂ := eq5894
       grind)
    | exact superpose eq5894 eq5895
    | exact resolve eq5895 eq5894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5894 eq5895
  have eq5897 : False := by grind
  exact eq5897

/-- `Equation639`: `x = x ◇ (y ◇ ((y ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_x_pxy_Equation639 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law639 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law639.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq81 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq87 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq204 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq80 X0 X0
       grind)
    | exact superpose eq80 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq80 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq80 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq12 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq208 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq204 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq211 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq208 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq208 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq208 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq4086 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq81 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq4087 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq4086 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4086
  have eq4090 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4087 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4087
    | (have j0 := eq4087 X0
       grind)
    | exact resolve eq4087 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4087
  have eq4093 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4090 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4090
    | exact resolve eq4090 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4090
  have eq4138 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4093 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq4093
    | (have j0 := eq4093 X0
       grind)
    | exact resolve eq4093 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4093
  have eq4140 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq4138 X0
       grind)
    | exact superpose eq4138 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq4138 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq4138 X0
       grind)
    | exact resolve eq12 eq4138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4138
  have eq4173 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq4140 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4140
  have eq4186 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq87
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq4233 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4186 X0 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq4186
    | (have j0 := eq4186 X0 X0
       grind)
    | exact resolve eq4186 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4186
  have eq4251 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4173 X0 X1
       grind)
    | exact superpose eq4173 eq11
    | (have j1 := eq4173 X0 X1
       grind)
    | exact resolve eq11 eq4173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4173
  have eq4360 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4251 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4251
    | (have j0 := eq4251 X0 X0
       grind)
    | exact resolve eq4251 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4251
  have eq4443 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4360 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4360
  have eq4444 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4443 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4443
  have eq4714 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq211 X0 X1
       have i₂ := eq4444 X0
       grind)
    | exact superpose eq4444 eq211
    | (have j0 := eq211 X0 X1
       grind)
    | exact resolve eq211 eq4444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq4724 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq205 X0 X0
       have i₂ := eq4444 X0
       grind)
    | exact superpose eq4444 eq205
    | (have j0 := eq205 X0 X0
       grind)
    | exact resolve eq205 eq4444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq4750 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4444 (σ X0)
       grind)
    | exact superpose eq4444 eq15
    | exact resolve eq15 eq4444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4783 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4724 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4724
  have eq4814 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4750 X0
       have i₂ := eq4444 X0
       grind)
    | exact superpose eq4444 eq4750
    | exact resolve eq4750 eq4444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4444 eq4750
  have eq7426 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (τ (k X2 X0)) = (τ (M.op X2 X0)) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq4233 X0 X2
       grind)
    | exact superpose eq4233 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq4233 X0 X2
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq4233 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq4233 X0 X0
       grind)
    | exact resolve eq12 eq4233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4233
  have eq7481 : ∀ X0 X1 X2 : G, (τ (k X2 X0)) = (τ (M.op X2 X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq7426 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7426
  have eq14011 : ∀ X0 X1 X2 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X2 X1) = (M.op X2 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq7481 X1 X2 X0
       grind)
    | exact superpose eq7481 eq11
    | (have j1 := eq7481 X1 X2 X0
       grind)
    | exact resolve eq11 eq7481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7481
  have eq14143 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X2 X1) = (M.op X2 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14011 X0 X1 X2
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq14011
    | (have j0 := eq14011 X0 X1 X0
       grind)
    | exact resolve eq14011 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14011
  have eq14361 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14143 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14143
  have eq14362 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14361 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14361
  have eq14649 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14362 X0 (τ X1)
       grind)
    | exact superpose eq14362 eq18
    | (have j1 := eq14362 X0 (τ X1)
       grind)
    | exact resolve eq18 eq14362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq14695 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14362 (σ X0) (σ X1)
       grind)
    | exact superpose eq14362 eq15
    | (have j1 := eq14362 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14362
  have eq16771 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14649 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14649
    | exact resolve eq14649 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14649
  have eq16902 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16771 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq16771
    | (have j0 := eq16771 X0 X1
       grind)
    | exact resolve eq16771 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16771
  have eq19824 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14695 x y
       grind)
    | exact superpose eq14695 eq16
    | (have j1 := eq14695 x y
       grind)
    | exact resolve eq16 eq14695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19914 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq14695 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14695
  have eq20187 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19914 (τ X0) (τ X1)
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq19914
    | (have j0 := eq19914 (τ X0) (τ X1)
       grind)
    | exact resolve eq19914 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq20267 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq20187 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq20187
    | (have j0 := eq20187 X0 X1
       grind)
    | exact resolve eq20187 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20187
  have eq20304 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq20267 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20267
    | (have j0 := eq20267 X0 X1
       grind)
    | exact resolve eq20267 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20267
  have eq20324 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20304 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq20304
    | (have j0 := eq20304 X0 X1
       grind)
    | exact resolve eq20304 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20304
  have eq20339 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20324 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20324
    | (have j0 := eq20324 X0 X1
       grind)
    | exact resolve eq20324 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20324
  have eq20949 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19824
       have i₂ := eq16902 y x
       grind)
    | exact superpose eq16902 eq19824
    | (have j1 := eq16902 (σ y) (σ x)
       grind)
    | (have r₁ := eq19824
       have r₂ := eq16902 y x
       grind)
    | exact resolve eq19824 eq16902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16902 eq19824
  have eq20952 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20949
  have eq21071 : x ≠ x ∨ x = (k x y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq20952
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq20952
       grind)
    | exact resolve eq13 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20952
  have eq21094 : x = (k x y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21071
  have eq27288 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19914 x y
       have i₂ := eq21094
       grind)
    | exact superpose eq21094 eq19914
    | (have j0 := eq19914 x y
       grind)
    | exact resolve eq19914 eq21094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19914 eq21094
  have eq27295 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq27288
  have eq27296 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq27295
  have eq27534 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27296
       grind)
    | exact superpose eq27296 eq16
    | exact resolve eq16 eq27296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27541 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq27296
       grind)
    | exact superpose eq27296 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq27296
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq27296
       grind)
    | exact resolve eq13 eq27296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27296
  have eq27566 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq27541
  have eq27577 : (σ x) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq27566
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq27566
    | exact resolve eq27566 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27566
  have eq27584 : y = (M.op y y) ∨ (σ x) = (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq27577
       have i₂ := eq4814 y
       grind)
    | exact superpose eq4814 eq27577
    | exact resolve eq27577 eq4814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27577
  have eq39311 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4783 y
       have i₂ := eq27584
       grind)
    | exact superpose eq27584 eq4783
    | (have j0 := eq4783 y
       grind)
    | (have r₁ := eq4783 y
       have r₂ := eq27584
       grind)
    | exact resolve eq4783 eq27584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27584
  have eq39357 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq39311
  have eq39384 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have j1 := eq4783 y
       grind)
    | (have r₁ := eq39357
       have r₂ := eq4783 y
       grind)
    | exact resolve eq39357 eq4783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39357
  have eq39397 : (σ x) = (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq39384
       have i₂ := eq4814 y
       grind)
    | exact superpose eq4814 eq39384
    | exact resolve eq39384 eq4814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39384
  have eq39581 : (k x y) = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq39397
       grind)
    | exact superpose eq39397 eq10
    | exact resolve eq10 eq39397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39397
  have eq39746 : x = (k x y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq39581
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq39581
    | exact resolve eq39581 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39581
  have eq39796 : x ≠ x ∨ x = (M.op x y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq20339 x y
       have i₂ := eq39746
       grind)
    | exact superpose eq39746 eq20339
    | (have j0 := eq20339 x y
       grind)
    | (have r₁ := eq20339 x y
       have r₂ := eq39746
       grind)
    | exact resolve eq20339 eq39746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20339 eq39746
  have eq39805 : x = (M.op x y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq39796
  have eq40024 : (σ x) ≠ (σ x) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq27534
       have i₂ := eq39805
       grind)
    | exact superpose eq39805 eq27534
    | exact resolve eq27534 eq39805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27534 eq39805
  have eq40059 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq40024
  have eq40078 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq4714 y X0
       have i₂ := eq40059
       grind)
    | exact superpose eq40059 eq4714
    | (have j0 := eq4714 y X0
       grind)
    | (have r₁ := eq4714 y x
       have r₂ := eq40059
       grind)
    | exact resolve eq4714 eq40059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40084 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4783 y
       have i₂ := eq40059
       grind)
    | exact superpose eq40059 eq4783
    | (have j0 := eq4783 y
       grind)
    | (have r₁ := eq4783 y
       have r₂ := eq40059
       grind)
    | exact resolve eq4783 eq40059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40059
  have eq40130 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq40084
  have eq40136 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq40078 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40078
  have eq40157 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq4783 y
       grind)
    | (have r₁ := eq40130
       have r₂ := eq4783 y
       grind)
    | exact resolve eq40130 eq4783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4783 eq40130
  have eq40161 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq40136 X0
       have j1 := eq4714 y X0
       grind)
    | (have r₁ := eq40136 X0
       have r₂ := eq4714 y x
       grind)
    | exact resolve eq40136 eq4714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4714 eq40136
  have eq40171 : (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq40157
       have i₂ := eq4814 y
       grind)
    | exact superpose eq4814 eq40157
    | exact resolve eq40157 eq4814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4814 eq40157
  have eq40379 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq40171
       grind)
    | exact superpose eq40171 eq10
    | exact resolve eq10 eq40171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40171
  have eq40549 : y = (M.op y y) := by
    first
    | (have i₁ := eq40379
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq40379
    | exact resolve eq40379 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40379
  have eq40689 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq40549
       grind)
    | exact superpose eq40549 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq40549
       grind)
    | exact resolve eq12 eq40549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40549
  have eq40761 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq40689 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40689
  have eq42486 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq40161 (σ X0)
       grind)
    | exact superpose eq40161 eq15
    | exact resolve eq15 eq40161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40161
  have eq42581 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq42486 X0
       have i₂ := eq40761 X0
       grind)
    | exact superpose eq40761 eq42486
    | exact resolve eq42486 eq40761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40761 eq42486
  have eq44004 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42581 x
       grind)
    | exact superpose eq42581 eq16
    | (have r₁ := eq16
       have r₂ := eq42581 x
       grind)
    | exact resolve eq16 eq42581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42581
  have eq44116 : False := by grind
  exact eq44116

/-- `Equation639`: `x = x ◇ (y ◇ ((y ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation639 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law639 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law639.models_iff G M).mp hM
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
  have eq3281 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
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
  have eq3322 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (k y (τ (σ x))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
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
  have eq3330 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y (τ (σ x))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3322
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq3322
    | exact resolve eq3322 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3322
  have eq3337 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3281 X0 X1
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq3281
    | (have j0 := eq3281 X0 X1
       grind)
    | exact resolve eq3281 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq3281
  have eq3340 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3330
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3330
    | exact resolve eq3330 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3330
  have eq3356 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq3337 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq3337 X0 X1
       grind)
    | exact superpose eq3337 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq3337 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq3337 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq3337 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq3337 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq3337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3384 : ∀ X0 X1 : G, (τ (k X1 (τ X0))) = (τ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0
       have i₂ := eq3337 X1 (τ X0)
       grind)
    | (have i₁ := eq30 X0
       have i₂ := eq3337 (τ X0) (τ X0)
       grind)
    | exact superpose eq3337 eq30
    | (have j1 := eq3337 X1 (τ X0)
       grind)
    | exact resolve eq30 eq3337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3337
  have eq3391 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3356 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3356
  have eq3392 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3391 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3391
  have eq3466 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq3392 X0 X1
       grind)
    | exact superpose eq3392 eq11
    | (have j1 := eq3392 X0 X1
       grind)
    | exact resolve eq11 eq3392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3392
  have eq3582 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3466 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq3466
    | (have j0 := eq3466 X0 X1
       grind)
    | exact resolve eq3466 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3466
  have eq3602 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3582 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3582
    | (have j0 := eq3582 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq3582 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3582
  have eq3760 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3602 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq3602
    | (have j0 := eq3602 X0 X1
       grind)
    | exact resolve eq3602 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3602
  have eq10747 : ∀ X0 X1 : G, (k X1 (τ X0)) = (σ (τ (M.op (τ X0) X1))) ∨ (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 (τ X0))
       have i₂ := eq3384 X0 X1
       grind)
    | exact superpose eq3384 eq11
    | (have j1 := eq3384 X0 X1
       grind)
    | exact resolve eq11 eq3384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3384
  have eq10876 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10747 X0 X1
       have i₂ := eq11 (M.op (τ X0) X1)
       grind)
    | exact superpose eq11 eq10747
    | (have j0 := eq10747 X0 X1
       grind)
    | exact resolve eq10747 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10747
  have eq11295 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq10876 X0 X1
       grind)
    | exact superpose eq10876 eq19
    | (have j1 := eq10876 X0 X1
       grind)
    | exact resolve eq19 eq10876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq10876
  have eq11391 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11295 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11295
    | exact resolve eq11295 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11295
  have eq11492 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11391 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq11391
    | (have j0 := eq11391 X0 X1
       grind)
    | exact resolve eq11391 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11391
  have eq11498 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11492 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq11492
    | (have j0 := eq11492 X0 X1
       grind)
    | exact resolve eq11492 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11492
  have eq15656 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3760 y x
       grind)
    | exact superpose eq3760 eq16
    | (have j1 := eq3760 y x
       grind)
    | exact resolve eq16 eq3760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3760
  have eq15775 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq15656
       have i₂ := eq11498 x y
       grind)
    | exact superpose eq11498 eq15656
    | (have j1 := eq11498 x y
       grind)
    | (have r₁ := eq15656
       have r₂ := eq11498 x y
       grind)
    | (have r₁ := eq15656
       have r₂ := eq11498 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq15656
       have r₂ := eq11498 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq15656 eq11498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11498 eq15656
  have eq15780 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq15775
  have eq15781 : x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq15780
  have eq15788 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15781
       grind)
    | exact superpose eq15781 eq16
    | exact resolve eq16 eq15781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15781
  have eq15789 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq15788
       have r₂ := eq22 x
       grind)
    | exact resolve eq15788 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15788
  have eq15791 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15789
       grind)
    | exact superpose eq15789 eq10
    | exact resolve eq10 eq15789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15789
  have eq15854 : x = y ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq15791
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15791
    | exact resolve eq15791 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15791
  have eq15856 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15854
       grind)
    | exact superpose eq15854 eq16
    | exact resolve eq16 eq15854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15854
  have eq15857 : (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq15856
       have r₂ := eq22 x
       grind)
    | exact resolve eq15856 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15856
  have eq15858 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3340
       have i₂ := eq15857
       grind)
    | exact superpose eq15857 eq3340
    | (have r₁ := eq3340
       have r₂ := eq15857
       grind)
    | exact resolve eq3340 eq15857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3340
  have eq15859 : (M.op x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq15857
       grind)
    | exact superpose eq15857 eq10
    | exact resolve eq10 eq15857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15903 : (σ x) = (σ y) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq15858
  have eq15923 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq15859
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq15859
    | exact resolve eq15859 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15859
  have eq15926 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq15923
       grind)
    | exact superpose eq15923 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq15923
       grind)
    | exact resolve eq13 eq15923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15923
  have eq15930 : x = y ∨ (k y x) = (M.op x x) := by grind
  clear eq15926
  have eq15932 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15930
       grind)
    | exact superpose eq15930 eq16
    | exact resolve eq16 eq15930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15930
  have eq15933 : (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq15932
       have r₂ := eq22 x
       grind)
    | exact resolve eq15932 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15932
  have eq17079 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15903
       grind)
    | exact superpose eq15903 eq16
    | exact resolve eq16 eq15903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15903
  have eq17165 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq17079
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq17079
    | exact resolve eq17079 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17079
  have eq17186 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq17165
       have r₂ := eq15857
       grind)
    | exact resolve eq17165 eq15857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17165
  have eq17187 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq17186
       have i₂ := eq15933
       grind)
    | exact superpose eq15933 eq17186
    | exact resolve eq17186 eq15933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15933 eq17186
  have eq17207 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq17187
       grind)
    | exact superpose eq17187 eq11
    | exact resolve eq11 eq17187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17187
  have eq17314 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17207
       grind)
    | exact superpose eq17207 eq16
    | exact resolve eq16 eq17207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17207
  have eq17346 : False := by grind
  exact eq17346

/-- `Equation653`: `x = x ◇ (y ◇ ((z ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation653 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law653 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law653.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq49 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
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
  have eq66 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq171 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq161 x y
       grind)
    | exact superpose eq161 eq16
    | (have j1 := eq161 x y
       grind)
    | exact resolve eq16 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq474 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq504 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq474 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq474
    | (have j0 := eq474 X0 X1
       grind)
    | exact resolve eq474 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq574 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq171
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq171
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq171
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq171
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq171 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq574
  have eq14865 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq575
       grind)
    | exact superpose eq575 eq16
    | exact resolve eq16 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq14866 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq14865
       have r₂ := eq22 x
       grind)
    | exact resolve eq14865 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14865
  have eq18485 : y = (τ (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq14866
       grind)
    | exact superpose eq14866 eq10
    | exact resolve eq10 eq14866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14866
  have eq18589 : x = y ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq18485
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18485
    | exact resolve eq18485 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18485
  have eq18591 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18589
       grind)
    | exact superpose eq18589 eq16
    | exact resolve eq16 eq18589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18589
  have eq18592 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq18591
       have r₂ := eq22 x
       grind)
    | exact resolve eq18591 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18591
  have eq18720 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18592
       grind)
    | exact superpose eq18592 eq16
    | exact resolve eq16 eq18592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18724 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq66 y (σ x)
       have i₂ := eq18592
       grind)
    | exact superpose eq18592 eq66
    | (have j0 := eq66 x (σ y)
       grind)
    | (have r₁ := eq66 y (σ x)
       have r₂ := eq18592
       grind)
    | exact resolve eq66 eq18592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq18592
  have eq18807 : (σ x) = (σ y) ∨ (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq18724
  have eq18810 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq18807
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq18807
    | exact resolve eq18807 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18807
  have eq19174 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq18810
       grind)
    | exact superpose eq18810 eq10
    | exact resolve eq10 eq18810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18810
  have eq19279 : x = y ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq19174
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19174
    | exact resolve eq19174 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19174
  have eq19500 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19279
       grind)
    | exact superpose eq19279 eq16
    | exact resolve eq16 eq19279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19279
  have eq19501 : (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq19500
       have r₂ := eq22 x
       grind)
    | exact resolve eq19500 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19500
  have eq19903 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq504 x y
       have i₂ := eq19501
       grind)
    | exact superpose eq19501 eq504
    | (have j0 := eq504 x y
       grind)
    | exact resolve eq504 eq19501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504 eq19501
  have eq19978 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq19903
  have eq20014 : x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq19978
       have r₂ := eq18720
       grind)
    | exact resolve eq19978 eq18720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18720 eq19978
  have eq20017 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20014
       grind)
    | exact superpose eq20014 eq16
    | exact resolve eq16 eq20014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20014
  have eq20018 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq20017
       have r₂ := eq22 x
       grind)
    | exact resolve eq20017 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20017
  have eq20387 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ (M.op x y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq20018
       grind)
    | exact superpose eq20018 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq20018
       grind)
    | exact resolve eq13 eq20018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22235 : (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have j0 := eq20387 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20387
  have eq22502 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq171
       have i₂ := eq22235
       grind)
    | exact superpose eq22235 eq171
    | exact resolve eq171 eq22235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq22235
  have eq22511 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq22502
  have eq22515 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq22511
       have i₂ := eq20018
       grind)
    | exact superpose eq20018 eq22511
    | exact resolve eq22511 eq20018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20018 eq22511
  have eq22518 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq22515
       have r₂ := eq16
       grind)
    | exact resolve eq22515 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22515
  have eq22521 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22518
       grind)
    | exact superpose eq22518 eq16
    | exact resolve eq16 eq22518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22518
  have eq22527 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq22521
       have r₂ := eq22 x
       grind)
    | exact resolve eq22521 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22521
  have eq22816 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq22527
       grind)
    | exact superpose eq22527 eq10
    | exact resolve eq10 eq22527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22527
  have eq22948 : x = y := by
    first
    | (have i₁ := eq22816
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22816
    | exact resolve eq22816 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22816
  have eq22975 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22948
       grind)
    | exact superpose eq22948 eq16
    | exact resolve eq16 eq22948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22948
  have eq22981 : False := by grind
  exact eq22981

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxx_pyy_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq14 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : y ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
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
  have eq64 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
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
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq75 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq93
    | exact resolve eq93 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq101 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq108 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq108 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq108 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq111 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq109 (σ X0)
       grind)
    | exact superpose eq109 eq10
    | exact resolve eq10 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq109 x
       grind)
    | exact superpose eq109 eq43
    | exact resolve eq43 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq113 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq109 y
       grind)
    | exact superpose eq109 eq73
    | exact resolve eq73 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq116 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq113
       have i₂ := eq109 sF3
       grind)
    | exact superpose eq109 eq113
    | exact resolve eq113 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq117 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq112
       have i₂ := eq109 sF2
       grind)
    | exact superpose eq109 eq112
    | exact resolve eq112 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq118 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq111 X0
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq111
    | exact resolve eq111 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq125 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq101
       have i₂ := eq109 sF3
       grind)
    | exact superpose eq109 eq101
    | exact resolve eq101 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq126 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq125
       have i₂ := eq109 y
       grind)
    | exact superpose eq109 eq125
    | exact resolve eq125 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq135 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq297 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq109 (τ X0)
       grind)
    | exact superpose eq109 eq34
    | exact resolve eq34 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq308 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq297 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq297
    | exact resolve eq297 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq310 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq308 X0
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq308
    | exact resolve eq308 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq382 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq11 X1 (τ X0)
       grind)
    | exact superpose eq11 eq38
    | (have j1 := eq11 X1 (τ X0)
       grind)
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq484 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq14 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq594 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X2 X0 X1
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq721 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq75 X1 X0
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq75 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq75 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq75 X0 X1
       grind)
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq728 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq721 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq729 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq728 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq734 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq729 X0 X1
       have i₂ := eq118 X0
       grind)
    | exact superpose eq118 eq729
    | (have j0 := eq729 X0 X1
       grind)
    | exact resolve eq729 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq752 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq734 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq734
    | (have j0 := eq734 X0 X1
       grind)
    | exact resolve eq734 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq792 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq310 X0
       grind)
    | exact superpose eq310 eq16
    | exact resolve eq16 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq987 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq594 X1 x X3
       have i₂ := eq594 X1 x X0
       grind)
    | exact superpose eq594 eq594
    | exact resolve eq594 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1001 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 x
       have i₂ := eq594 X1 x X0
       grind)
    | exact superpose eq594 eq14
    | exact resolve eq14 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1013 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 (M.op X2 X0) X2
       have i₂ := eq594 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq594 eq53
    | exact resolve eq53 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1020 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1013 X0 X1 X2
       have i₂ := eq53 X0 X0 X1
       grind)
    | exact superpose eq53 eq1013
    | exact resolve eq1013 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq1036 : y = (M.op y (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq1001 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1001
    | (have j0 := eq1001 x y
       grind)
    | exact resolve eq1001 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1037 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq1001
    | (have j0 := eq1001 (σ x) (σ y)
       grind)
    | exact resolve eq1001 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1042 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1001 X0 (M.op X0 X0)
       have i₂ := eq1001 X0 X0
       grind)
    | exact superpose eq1001 eq1001
    | exact resolve eq1001 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1049 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    by_contra hcon
    push Not at hcon
    have f1049_12 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
      intro X0 X1 X2
      grind
    have f1049_13 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
      intro X0 X1
      grind
    have f1049_22 : (M.op X0 (M.op X1 (M.op X1 X0))) ≠ (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by grind
    have f1049_60 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
      intro X0 X1 X2
      first
      | (have i₁ := f1049_12 (M.op X0 (M.op X0 X1)) X1 X1
         have i₂ := f1049_13 X0 X1
         grind)
      | exact superpose f1049_13 f1049_12
      | exact resolve f1049_12 f1049_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1049_75 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
      intro X0 X1 X2
      first
      | (have i₁ := f1049_60 X1 X0 X2
         have i₂ := f1049_13 X0 X1
         grind)
      | exact superpose f1049_13 f1049_60
      | exact resolve f1049_60 f1049_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1049_126 : X0 ≠ (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) := by
      first
      | (have i₁ := f1049_22
         have i₂ := f1049_13 X1 X0
         grind)
      | exact superpose f1049_13 f1049_22
      | exact resolve f1049_22 f1049_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1049_127 : False := by
      first
      | (have r₁ := f1049_126
         have r₂ := f1049_75 X0 X1 X2
         grind)
      | exact resolve f1049_126 f1049_75
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f1049_127
  have eq1054 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    by_contra hcon
    push Not at hcon
    have f1054_12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
      intro X0 X1 X2
      grind
    have f1054_13 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
      intro X0 X1
      grind
    have f1054_22 : X0 ≠ (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) := by grind
    have f1054_23 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
      intro X0 X1 X2
      first
      | (have i₁ := f1054_12 X1 X0 X2
         have i₂ := f1054_13 X0 X1
         grind)
      | exact superpose f1054_13 f1054_12
      | exact resolve f1054_12 f1054_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1054_71 : X0 ≠ X0 := by
      first
      | (have i₁ := f1054_22
         have i₂ := f1054_23 X0 X1 X2
         grind)
      | exact superpose f1054_23 f1054_22
      | (have r₁ := f1054_22
         have r₂ := f1054_23 X0 X1 X2
         grind)
      | exact resolve f1054_22 f1054_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1054_75 : False := by grind
    exact f1054_75
  clear eq1049
  have eq1060 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op X0 (M.op y (M.op x (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq1036 eq14
    | exact resolve eq14 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1062 : ∀ X0 : G, (M.op y (M.op x (M.op x y))) = (M.op (M.op X0 (M.op y (M.op x (M.op x y)))) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1036 eq53
    | exact resolve eq53 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1068 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1036 eq1062
    | exact resolve eq1062 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1070 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq1036 eq1060
    | exact resolve eq1060 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060
  have eq1073 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op X0 (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))))) := by
    intro X0
    first
    | exact superpose eq1037 eq14
    | exact resolve eq14 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1083 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1037 eq1073
    | exact resolve eq1073 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq1170 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1 X0
       have i₂ := eq1042 X0
       grind)
    | exact superpose eq1042 eq53
    | exact resolve eq53 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1171 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq1042 X0
       grind)
    | exact superpose eq1042 eq14
    | exact resolve eq14 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1245 : y = (M.op (M.op x y) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq1068 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1068
    | (have j0 := eq1068 x
       grind)
    | exact resolve eq1068 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1455 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1171 (σ X0) X1
       have i₂ := eq118 X0
       grind)
    | exact superpose eq118 eq1171
    | exact resolve eq1171 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1456 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1171 (τ X0) X1
       have i₂ := eq792 X0
       grind)
    | exact superpose eq792 eq1171
    | exact resolve eq1171 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq1724 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq1036 eq987
    | exact resolve eq987 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1728 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq1037 eq987
    | exact resolve eq987 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1963 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1020 X0 X1 X0
       have i₂ := eq1042 X0
       grind)
    | exact superpose eq1042 eq1020
    | exact resolve eq1020 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020 eq1042
  have eq2417 : (M.op y (M.op x (M.op x y))) = (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) := by
    first
    | exact superpose eq1036 eq1963
    | exact resolve eq1963 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2422 : (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1037 eq1963
    | exact resolve eq1963 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2454 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1001 (M.op X1 X0) X0
       have i₂ := eq1963 X0 X1
       grind)
    | exact superpose eq1963 eq1001
    | exact resolve eq1001 eq1963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2481 : (σ y) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1037 eq2422
    | exact resolve eq2422 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037 eq2422
  have eq2484 : y = (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) := by
    first
    | exact superpose eq1036 eq2417
    | exact resolve eq2417 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2417
  have eq3209 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X1) = (M.op (M.op X0 (M.op X0 X1)) (M.op X3 (M.op X3 (M.op (M.op X2 X1) X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1054 (M.op (M.op X2 X1) X1) X3 X1
       have i₂ := eq594 X1 X2 X0
       grind)
    | exact superpose eq594 eq1054
    | exact resolve eq1054 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq3398 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3209 X0 X1 X2 x
       have i₂ := eq14 X1 x X2
       grind)
    | exact superpose eq14 eq3209
    | exact resolve eq3209 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3209
  have eq3417 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3398 X0 X1 x
       have i₂ := eq1963 X1 x
       grind)
    | exact superpose eq1963 eq3398
    | exact resolve eq3398 eq1963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3398
  have eq3636 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op x (M.op x y))) (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq1724 (M.op x (M.op x sF0))
       have i₂ := eq1963 (M.op x sF0) x
       grind)
    | exact superpose eq1963 eq1724
    | exact resolve eq1724 eq1963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724
  have eq3685 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op x (M.op x y))) y) := by
    intro X0
    first
    | exact superpose eq2484 eq3636
    | exact resolve eq3636 eq2484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3636
  have eq3694 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq1728 (M.op x (M.op sF2 sF4))
       have i₂ := eq1963 (M.op sF2 sF4) x
       grind)
    | exact superpose eq1963 eq1728
    | exact resolve eq1728 eq1963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3743 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) (σ y)) := by
    intro X0
    first
    | exact superpose eq2481 eq3694
    | exact resolve eq3694 eq2481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3694
  have eq4152 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq484 X0 X1 X1
       have i₂ := eq1963 X0 X1
       grind)
    | exact superpose eq1963 eq484
    | exact resolve eq484 eq1963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq4153 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4152 X0 x
       have i₂ := eq1963 (M.op X0 X0) x
       grind)
    | exact superpose eq1963 eq4152
    | exact resolve eq4152 eq1963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4152
  have eq4201 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4153 (M.op X0 X0)
       have i₂ := eq4153 X0
       grind)
    | exact superpose eq4153 eq4153
    | exact resolve eq4153 eq4153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4257 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq4201 X0
       have i₂ := eq1054 X0 X0 X0
       grind)
    | exact superpose eq1054 eq4201
    | exact resolve eq4201 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4201
  have eq4475 : ∀ X0 : G, (σ (M.op x (M.op x y))) = (M.op X0 (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq2484 eq1455
    | exact resolve eq1455 eq2484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4546 : ∀ X0 : G, (σ (M.op x (M.op x y))) = (M.op X0 (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq4475 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4475
    | (have j0 := eq4475 X0
       grind)
    | exact resolve eq4475 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4475
  have eq4559 : (σ (M.op x (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1083 eq4546
    | (have j0 := eq4546 (σ x)
       grind)
    | exact resolve eq4546 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4546
  have eq4663 : (M.op x (M.op x y)) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq4559 eq16
    | exact resolve eq16 eq4559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5504 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3743 sF2
       have i₂ := eq987 sF2 sF4 x
       grind)
    | (have i₁ := eq3743 sF2
       have i₂ := eq987 X0 sF4 sF2
       grind)
    | exact superpose eq987 eq3743
    | exact resolve eq3743 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3743
  have eq5844 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op x X0)) ∨ (M.op x X0) = (M.op X0 x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq382
    | exact resolve eq382 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq5910 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op x X0)) ∨ (M.op x X0) = (M.op X0 x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | exact superpose eq39 eq5844
    | (have j0 := eq5844 X0
       grind)
    | exact resolve eq5844 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq5844
  have eq7234 : ∀ X0 : G, (σ (k (k (M.op x y) y) X0)) = (M.op (σ X0) (k (σ (M.op x y)) (σ y))) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ X0) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op X0 X0)) = (σ (k (k (M.op x y) y) X0)) := by
    intro X0
    first
    | exact superpose eq135 eq752
    | (have j0 := eq752 X0 (k (M.op x y) y)
       grind)
    | exact resolve eq752 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq752
  have eq19015 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19016 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq19015
    | exact resolve eq19015 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19015
  have eq19027 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq19016
       have r₂ := eq27
       grind)
    | exact resolve eq19016 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19016
  have eq19031 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq19027
    | exact resolve eq19027 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19027
  have eq19033 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq19031
    | exact resolve eq19031 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19031
  have eq19036 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19033 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq19033
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq19033
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq19033
       grind)
    | exact resolve eq12 eq19033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19033
  have eq19055 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq19036
       have r₂ := eq26
       grind)
    | exact resolve eq19036 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19036
  have eq19057 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq19055
    | exact resolve eq19055 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19055
  have eq19058 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq19057
  have eq19102 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19058 eq96
    | exact resolve eq96 eq19058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq19058
  have eq19110 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19102
  have eq19137 : ∀ X0 : G, (τ (σ x)) = (M.op X0 (M.op X0 (τ (σ (M.op x y))))) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq19110 eq1456
    | exact resolve eq1456 eq19110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19140 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19110 eq4153
    | exact resolve eq4153 eq19110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19110
  have eq19177 : ∀ X0 : G, (τ (σ x)) = (M.op X0 (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30 eq19137
    | exact resolve eq19137 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq19137
  have eq19185 : ∀ X0 : G, x = (M.op X0 (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq28 eq19177
    | exact resolve eq19177 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq19177
  have eq20092 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19185 eq3685
    | exact resolve eq3685 eq19185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3685 eq19185
  have eq20114 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20092
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20092
    | exact resolve eq20092 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20092
  have eq20291 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1455 y X0
       have i₂ := eq20114
       grind)
    | exact superpose eq20114 eq1455
    | exact resolve eq1455 eq20114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20114
  have eq20339 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq20291
    | (have j0 := eq20291 X0
       grind)
    | exact resolve eq20291 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20291
  have eq20350 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq20339 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20339
    | (have j0 := eq20339 X0
       grind)
    | exact resolve eq20339 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20339
  have eq21829 : (σ y) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19140 eq20350
    | exact resolve eq20350 eq19140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19140 eq20350
  have eq21877 : (σ y) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq21829
  have eq25319 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21877 eq1171
    | exact resolve eq1171 eq21877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21877
  have eq25360 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq25319
    | exact resolve eq25319 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25319
  have eq25366 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq25360
       have r₂ := eq27
       grind)
    | exact resolve eq25360 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25360
  have eq25376 : ∀ X0 : G, x = (M.op X0 (M.op X0 (M.op (M.op x y) x))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq25366
       grind)
    | exact superpose eq25366 eq14
    | exact resolve eq14 eq25366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25381 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op X0 (M.op X0 x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq987 y x X0
       have i₂ := eq25366
       grind)
    | exact superpose eq25366 eq987
    | exact resolve eq987 eq25366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25827 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 (M.op X1 (M.op X0 (M.op (M.op x y) x)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq25376 eq987
    | exact resolve eq987 eq25376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25896 : x = (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4257 x
       have i₂ := eq25381 x
       grind)
    | exact superpose eq25381 eq4257
    | exact resolve eq4257 eq25381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25381
  have eq26237 : ∀ X0 : G, (σ (M.op y (M.op x y))) = (M.op X0 (M.op X0 (σ x))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq25896 eq1455
    | exact resolve eq1455 eq25896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25896
  have eq26280 : ∀ X0 : G, (σ (M.op y (M.op x y))) = (M.op X0 (M.op X0 (σ x))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq26237 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26237
    | (have j0 := eq26237 X0
       grind)
    | exact resolve eq26237 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26237
  have eq26694 : (σ x) = (M.op (σ x) (σ (M.op y (M.op x y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26280 eq1001
    | exact resolve eq1001 eq26280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26280
  have eq38577 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) x)) = (M.op (M.op X0 x) (M.op X0 x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f38577_14 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
      intro X0
      grind
    have f38577_15 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 (M.op X1 (M.op X0 (M.op (M.op x y) x)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      grind
    have f38577_24 : (M.op X0 (M.op (M.op x y) x)) ≠ (M.op (M.op X0 x) (M.op X0 x)) := by grind
    have f38577_25 : y ≠ (M.op x y) := by grind
    have f38577_26 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f38577_27 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 (M.op X1 (M.op X0 (M.op (M.op x y) x)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      first
      | (have j0 := f38577_15 X0 X1
         grind)
      | (have r₁ := f38577_15 X0 X1
         have r₂ := f38577_25
         grind)
      | exact resolve f38577_15 f38577_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f38577_28 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 (M.op X1 (M.op X0 (M.op (M.op x y) x)))) := by
      intro X0 X1
      first
      | (have j0 := f38577_27 X0 X1
         grind)
      | (have r₁ := f38577_27 X0 X1
         have r₂ := f38577_26
         grind)
      | exact resolve f38577_27 f38577_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f38577_84 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) x)) = (M.op (M.op X0 x) (M.op X0 x)) := by
      intro X0
      first
      | (have i₁ := f38577_14 (M.op X0 (M.op (M.op x y) x))
         have i₂ := f38577_28 X0 (M.op X0 (M.op (M.op x y) x))
         grind)
      | exact superpose f38577_28 f38577_14
      | exact resolve f38577_14 f38577_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f38577_260 : (M.op X0 (M.op (M.op x y) x)) ≠ (M.op X0 (M.op (M.op x y) x)) := by
      first
      | (have i₁ := f38577_24
         have i₂ := f38577_84 X0
         grind)
      | exact superpose f38577_84 f38577_24
      | (have r₁ := f38577_24
         have r₂ := f38577_84 X0
         grind)
      | exact resolve f38577_24 f38577_84
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f38577_276 : False := by grind
    exact f38577_276
  clear eq4257 eq25827
  have eq72584 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op (M.op x y) x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq38577 y
       have i₂ := eq25366
       grind)
    | exact superpose eq25366 eq38577
    | exact resolve eq38577 eq25366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25366 eq38577
  have eq72734 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op (M.op x y) x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq72584
  have eq72790 : x = (M.op y (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72734 eq25376
    | exact resolve eq25376 eq72734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25376 eq72734
  have eq72817 : x = (M.op y (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq72790
  have eq72834 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72817 eq1170
    | exact resolve eq1170 eq72817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170 eq72817
  have eq72913 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (σ (M.op x (M.op x y))))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq72834 eq1455
    | exact resolve eq1455 eq72834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1455
  have eq72949 : (M.op x (M.op x y)) = (M.op (M.op (M.op x y) (M.op x (M.op x y))) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72834 eq3417
    | exact resolve eq3417 eq72834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3417 eq72834
  have eq72968 : (M.op x (M.op x y)) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1245 eq72949
    | exact resolve eq72949 eq1245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1245 eq72949
  have eq72982 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq4559 eq72913
    | exact resolve eq72913 eq4559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72913
  have eq73001 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1728 eq72982
    | exact resolve eq72982 eq1728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1728 eq72982
  have eq73008 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq73001
    | exact resolve eq73001 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73001
  have eq79224 : (σ x) = (M.op (σ x) (σ (M.op x (M.op x y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72968 eq26694
    | exact resolve eq26694 eq72968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26694 eq72968
  have eq79393 : (σ x) = (M.op (σ x) (σ (M.op x (M.op x y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq79224
  have eq79455 : (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4559 eq79393
    | exact resolve eq79393 eq4559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79393
  have eq91704 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq79455 eq5504
    | exact resolve eq5504 eq79455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5504 eq79455
  have eq91745 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq91704
    | exact resolve eq91704 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91704
  have eq92843 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq91745 eq73008
    | exact resolve eq73008 eq91745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73008 eq91745
  have eq92911 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq92843
  have eq92936 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq92911
       have r₂ := eq27
       grind)
    | exact resolve eq92911 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92911
  have eq92941 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq92936 eq27
    | exact resolve eq27 eq92936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92943 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq92936 eq64
    | (have r₁ := eq64
       have r₂ := eq92936
       grind)
    | exact resolve eq64 eq92936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq92953 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq92936 eq2481
    | exact resolve eq2481 eq92936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92957 : (M.op x (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq92936 eq4663
    | exact resolve eq4663 eq92936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4663
  have eq93011 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq92943
  have eq93031 : (M.op x (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq92957
    | exact resolve eq92957 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92957
  have eq93035 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq92953
    | exact resolve eq92953 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92953
  have eq93057 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq92936 eq93035
    | exact resolve eq93035 eq92936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92936 eq93035
  have eq93127 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq93057
  have eq94560 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (M.op X0 (τ (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq93127 eq1456
    | exact resolve eq1456 eq93127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94592 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq93127 eq2454
    | exact resolve eq2454 eq93127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2454
  have eq94617 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1083 eq94592
    | exact resolve eq94592 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083 eq94592
  have eq94627 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq94560
    | exact resolve eq94560 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq94560
  have eq94657 : y = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq94627 x
       have i₂ := eq1070 x
       grind)
    | (have i₁ := eq94627 x
       have i₂ := eq1070 x
       grind)
    | exact superpose eq1070 eq94627
    | (have j0 := eq94627 x
       grind)
    | exact resolve eq94627 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070 eq94627
  have eq95685 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq94617 eq1001
    | exact resolve eq1001 eq94617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94617
  have eq95721 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq95685
    | exact resolve eq95685 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95685
  have eq98167 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq94657 eq987
    | exact resolve eq987 eq94657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98168 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq94657 eq1001
    | exact resolve eq1001 eq94657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98171 : ∀ X0 : G, (M.op x y) = (M.op y (M.op X0 (M.op X0 (M.op x y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq94657 eq1054
    | exact resolve eq1054 eq94657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054
  have eq98173 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq94657 eq1963
    | exact resolve eq1963 eq94657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94657
  have eq98205 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq98168
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98168
    | exact resolve eq98168 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98168
  have eq98206 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq98167 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98167
    | (have j0 := eq98167 X0
       grind)
    | exact resolve eq98167 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98167
  have eq98239 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op X0 (M.op X0 (τ (M.op (σ x) (σ y))))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq95721 eq1456
    | exact resolve eq1456 eq95721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1456 eq95721
  have eq100142 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (M.op X0 (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq98205 eq987
    | exact resolve eq987 eq98205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987 eq98205
  have eq100854 : (M.op (M.op x y) (M.op x y)) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq93031 eq1963
    | exact resolve eq1963 eq93031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1963
  have eq102060 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq93011 eq92
    | exact resolve eq92 eq93011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq93011
  have eq102114 : (k y x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq126 eq102060
    | exact resolve eq102060 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq102060
  have eq102119 : (k y x) = (M.op y y) := by
    first
    | (have r₁ := eq102114
       have r₂ := eq63
       grind)
    | exact resolve eq102114 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq102114
  have eq102130 : (k (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq102119
       grind)
    | exact superpose eq102119 eq72
    | exact resolve eq72 eq102119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102119
  have eq102176 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq102130
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq102130
    | exact resolve eq102130 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq102130
  have eq137426 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq100854 eq98206
    | exact resolve eq98206 eq100854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98206 eq100854
  have eq137450 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq137426
  have eq140702 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq137450 eq1171
    | exact resolve eq1171 eq137450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171 eq137450
  have eq146745 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq5910 y
       grind)
    | exact superpose eq5910 eq72
    | (have j1 := eq5910 y
       grind)
    | exact resolve eq72 eq5910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5910
  have eq146998 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq102176 eq146745
    | exact resolve eq146745 eq102176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146745
  have eq147012 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq146998
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq146998
    | exact resolve eq146998 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146998
  have eq147024 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq147012
    | exact resolve eq147012 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147012
  have eq147031 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq147024
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq147024
    | exact resolve eq147024 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147024
  have eq147038 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq147031
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq147031
    | exact resolve eq147031 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147031
  have eq172719 : (M.op x y) = (M.op y (M.op (τ (M.op (σ x) (σ y))) (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq140702 eq98171
    | exact resolve eq98171 eq140702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98171 eq140702
  have eq172825 : (M.op x y) = (M.op y (M.op (τ (M.op (σ x) (σ y))) (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq172719
  have eq198800 : (M.op (M.op x y) (M.op x y)) = (M.op x (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq93031 eq100142
    | exact resolve eq100142 eq93031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93031 eq100142
  have eq198952 : (M.op (M.op x y) (M.op x y)) = (M.op x (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by grind
  clear eq198800
  have eq198996 : (τ (M.op (σ x) (σ y))) = (M.op x (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq198952 eq98239
    | exact resolve eq98239 eq198952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98239 eq198952
  have eq199020 : (τ (M.op (σ x) (σ y))) = (M.op x (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq198996
  have eq199278 : (τ (M.op (σ x) (σ y))) = (M.op x (M.op y (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq98173 eq199020
    | exact resolve eq199020 eq98173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98173 eq199020
  have eq199325 : (τ (M.op (σ x) (σ y))) = (M.op x (M.op y (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq199278
  have eq463179 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq147038 eq93127
    | exact resolve eq93127 eq147038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93127 eq147038
  have eq463440 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq463179
  have eq463483 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq463440
       have r₂ := eq92941
       grind)
    | exact resolve eq463440 eq92941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92941 eq463440
  have eq463559 : x = (M.op x (M.op y (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1001 y x
       have i₂ := eq463483
       grind)
    | exact superpose eq463483 eq1001
    | exact resolve eq1001 eq463483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001 eq463483
  have eq464356 : x = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq463559 eq199325
    | exact resolve eq199325 eq463559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199325 eq463559
  have eq464394 : x = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq464356
  have eq466370 : (M.op x y) = (M.op y (M.op x (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq464394 eq172825
    | exact resolve eq172825 eq464394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172825 eq464394
  have eq466781 : (M.op x y) = (M.op y (M.op x (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq466370
  have eq466853 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1036 eq466781
    | exact resolve eq466781 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036 eq466781
  have eq466854 : y = (M.op x y) := by grind
  clear eq466853
  have eq466879 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq466854 eq20
    | exact resolve eq20 eq466854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq467003 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq466854 eq2484
    | exact resolve eq2484 eq466854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2484
  have eq467053 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq466854 eq4559
    | exact resolve eq4559 eq466854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4559
  have eq467106 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq467053
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq467053
    | exact resolve eq467053 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467053
  have eq467155 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq467003
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq467003
    | exact resolve eq467003 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq467003
  have eq467270 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq466879
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq466879
    | exact resolve eq466879 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq466879
  have eq467289 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20 eq467106
    | exact resolve eq467106 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq467106
  have eq467304 : y = (M.op y y) := by
    first
    | exact superpose eq466854 eq467155
    | exact resolve eq467155 eq466854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467155
  have eq468617 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq467270 eq26
    | exact resolve eq26 eq467270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq469366 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq467289 eq2481
    | exact resolve eq2481 eq467289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2481 eq467289
  have eq469543 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq467270 eq469366
    | exact resolve eq469366 eq467270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469366
  have eq475127 : ∀ X0 : G, (σ (k (k (M.op x y) y) X0)) = (M.op (σ X0) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ X0) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op X0 X0)) = (σ (k (k (M.op x y) y) X0)) := by
    intro X0
    first
    | exact superpose eq467270 eq7234
    | (have j0 := eq7234 X0
       grind)
    | exact resolve eq7234 eq467270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7234
  have eq475128 : ∀ X0 : G, (σ (k (k (M.op x y) y) X0)) = (M.op (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ X0) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op X0 X0)) = (σ (k (k (M.op x y) y) X0)) := by
    intro X0
    first
    | (have i₁ := eq475127 X0
       have i₂ := eq109 sF1
       grind)
    | exact superpose eq109 eq475127
    | (have j0 := eq475127 X0
       grind)
    | exact resolve eq475127 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475127
  have eq475129 : ∀ X0 : G, (M.op (σ X0) (σ (M.op x y))) = (σ (k (k (M.op x y) y) X0)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ X0) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op X0 X0)) = (σ (k (k (M.op x y) y) X0)) := by
    intro X0
    first
    | exact superpose eq469543 eq475128
    | (have j0 := eq475128 X0
       grind)
    | exact resolve eq475128 eq469543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475128
  have eq475130 : ∀ X0 : G, (σ (k (k y y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ X0) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op X0 X0)) = (σ (k (k (M.op x y) y) X0)) := by
    intro X0
    first
    | exact superpose eq466854 eq475129
    | (have j0 := eq475129 X0
       grind)
    | exact resolve eq475129 eq466854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475129
  have eq475131 : ∀ X0 : G, (M.op (σ X0) (σ (M.op x y))) = (σ (k (M.op y y) X0)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ X0) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op X0 X0)) = (σ (k (k (M.op x y) y) X0)) := by
    intro X0
    first
    | (have i₁ := eq475130 X0
       have i₂ := eq109 y
       grind)
    | exact superpose eq109 eq475130
    | (have j0 := eq475130 X0
       grind)
    | exact resolve eq475130 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475130
  have eq475132 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ X0) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op X0 X0)) = (σ (k (k (M.op x y) y) X0)) := by
    intro X0
    first
    | (have i₁ := eq475131 X0
       have i₂ := eq467304
       grind)
    | exact superpose eq467304 eq475131
    | (have j0 := eq475131 X0
       grind)
    | exact resolve eq475131 eq467304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475131
  have eq475133 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ X0) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op X0 X0)) = (σ (k (k (M.op x y) y) X0)) := by
    intro X0
    first
    | exact superpose eq467270 eq475132
    | (have j0 := eq475132 X0
       grind)
    | exact resolve eq475132 eq467270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475132
  have eq475134 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op X0 X0)) = (σ (k (k (M.op x y) y) X0)) := by
    intro X0
    first
    | (have i₁ := eq475133 X0
       have i₂ := eq109 sF1
       grind)
    | exact superpose eq109 eq475133
    | (have j0 := eq475133 X0
       grind)
    | exact resolve eq475133 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475133
  have eq475135 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op X0 X0)) = (σ (k (k (M.op x y) y) X0)) := by
    intro X0
    first
    | exact superpose eq469543 eq475134
    | (have j0 := eq475134 X0
       grind)
    | exact resolve eq475134 eq469543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475134
  have eq475136 : ∀ X0 : G, (σ (k (k y y) X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq466854 eq475135
    | (have j0 := eq475135 X0
       grind)
    | exact resolve eq475135 eq466854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466854 eq475135
  have eq475137 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k (M.op y y) X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq475136 X0
       have i₂ := eq109 y
       grind)
    | exact superpose eq109 eq475136
    | (have j0 := eq475136 X0
       grind)
    | exact resolve eq475136 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq475136
  have eq475138 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq475137 X0
       have i₂ := eq467304
       grind)
    | exact superpose eq467304 eq475137
    | (have j0 := eq475137 X0
       grind)
    | exact resolve eq475137 eq467304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467304 eq475137
  have eq475147 : (k (σ y) (σ x)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq475138 x
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq475138
    | (have j0 := eq475138 x
       grind)
    | exact resolve eq475138 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq475138
  have eq476340 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq475147
       have i₂ := eq117
       grind)
    | exact superpose eq117 eq475147
    | exact resolve eq475147 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq475147
  have eq476624 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq102176 eq476340
    | exact resolve eq476340 eq102176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476340
  have eq476859 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq467270 eq476624
    | exact resolve eq476624 eq467270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476624
  have eq476999 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq469543 eq476859
    | exact resolve eq476859 eq469543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476859
  have eq477118 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq476999
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq476999
    | exact resolve eq476999 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476999
  have eq477215 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq468617 eq477118
    | exact resolve eq477118 eq468617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477118
  have eq477279 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq477215
       have r₂ := eq27
       grind)
    | exact resolve eq477215 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477215
  have eq477318 : (k (σ y) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq477279
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq477279
    | exact resolve eq477279 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq477279
  have eq477358 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq468617 eq477318
    | exact resolve eq477318 eq468617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477318
  have eq477380 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq102176 eq477358
    | exact resolve eq477358 eq102176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102176 eq477358
  have eq477400 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq467270 eq477380
    | exact resolve eq477380 eq467270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467270 eq477380
  have eq477420 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq469543 eq477400
    | exact resolve eq477400 eq469543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477400
  have eq477430 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq477420
       have r₂ := eq27
       grind)
    | exact resolve eq477420 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477420
  have eq477512 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq477430 eq4153
    | exact resolve eq4153 eq477430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4153 eq477430
  have eq477601 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq469543 eq477512
    | exact resolve eq477512 eq469543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469543 eq477512
  have eq477625 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq468617 eq477601
    | exact resolve eq477601 eq468617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468617 eq477601
  have eq477642 : False := by grind
  exact eq477642

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyx_pyx_x_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq9 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op X1 (M.op (M.op X2 X0) X0)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 (M.op X0 (M.op (M.op X2 X0) X0)) X0
       have r₂ := eq9 X0 X0 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (k (M.op X0 (M.op (M.op X1 X0) X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq9 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2))) (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2))) X1
       have i₂ := eq62 (M.op (M.op X1 X2) X2) X3 X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X2) (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77 X0 X1 X2 x
       have i₂ := eq72 (M.op (M.op X1 X2) X2) x X0
       grind)
    | exact superpose eq72 eq77
    | exact resolve eq77 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq79 : ∀ X1 X2 : G, (M.op (M.op (M.op X1 X2) X2) (M.op X2 (M.op (M.op X1 X2) X2))) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq78 x X1 X2
       have i₂ := eq72 X2 x X1
       grind)
    | exact superpose eq72 eq78
    | exact resolve eq78 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq78
  have eq176 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) ≠ (M.op X1 X1) ∨ (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op X0 X1) X1)) ∨ (k X1 (M.op X2 (M.op (M.op X0 X1) X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X1 (M.op (M.op X2 X0) X0))
       have i₂ := eq62 X0 X1 X2
       grind)
    | exact superpose eq62 eq13
    | (have j0 := eq13 X1 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) ≠ X0 ∨ (k (M.op X0 (M.op (M.op X1 X0) X0)) (M.op (M.op X1 X0) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op x (M.op (M.op X1 x) x)) (M.op (M.op X1 x) x)
       have i₂ := eq79 X1 x
       grind)
    | exact superpose eq79 eq12
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq544 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq552 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = X2 ∨ (k X1 X2) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X2
       have j1 := eq14 X1 X0
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
  have eq563 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq544 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq566 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq563 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq563 (k X0 X0) X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq563 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq563 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq569 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = X2 ∨ (k X1 X2) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq552 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq552 X0 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq552 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq552 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq571 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq565 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq565 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq565 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq565 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq565 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq575 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq571 X0 X1
       have j1 := eq566 X1 X0
       grind)
    | (have r₁ := eq571 X1 X0
       have r₂ := eq566 X0 X1
       grind)
    | (have r₁ := eq571 X0 (M.op X1 X1)
       have r₂ := eq566 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq571 (M.op X1 X1) X1
       have r₂ := eq566 (k (M.op X1 X1) X1) X1
       grind)
    | exact resolve eq571 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq578 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq566 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq581 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq578 (σ X0)
       grind)
    | exact superpose eq578 eq28
    | exact resolve eq28 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq586 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq578 (τ X0)
       grind)
    | exact superpose eq578 eq17
    | exact resolve eq17 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq575 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq575
    | exact resolve eq575 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq575 X1 (τ X0)
       grind)
    | exact superpose eq575 eq18
    | (have j1 := eq575 X1 (τ X0)
       grind)
    | exact resolve eq18 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq616 : ∀ X0 X1 : G, (τ X1) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq575 (τ X1) X0
       grind)
    | exact superpose eq575 eq17
    | (have j1 := eq575 (τ X1) X0
       grind)
    | exact resolve eq17 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq625 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq575 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq637 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) ≠ X1 ∨ (k X1 (M.op X2 (M.op (M.op X0 X1) X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq625 X1 (M.op X2 (M.op (M.op X0 X1) X1))
       have i₂ := eq62 X1 X2 X0
       grind)
    | exact superpose eq62 eq625
    | (have j0 := eq625 X1 (M.op X0 X1)
       grind)
    | exact resolve eq625 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq651 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X0 X2 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))) (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op X3 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))))) = (M.op X4 (M.op X4 (M.op X3 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq651 (M.op X3 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))) X3 X4
       have i₂ := eq61 X2 X3 X0 X1
       grind)
    | exact superpose eq61 eq651
    | exact resolve eq651 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq678 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X0) X0)) (M.op X0 (M.op X0 (M.op (M.op X1 X0) X0)))) = (M.op X2 (M.op X2 (M.op X0 (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq651 (M.op X0 (M.op (M.op X1 X0) X0)) (M.op (M.op X1 X0) X0) X2
       have i₂ := eq79 X1 X0
       grind)
    | exact superpose eq79 eq651
    | exact resolve eq651 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq679 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq651 X1 x X3
       have i₂ := eq651 X1 x X0
       grind)
    | exact superpose eq651 eq651
    | exact resolve eq651 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X1 X1 X2
       have i₂ := eq651 X1 X2 X0
       grind)
    | exact superpose eq651 eq62
    | exact resolve eq62 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq687 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 x
       have i₂ := eq651 X1 x X0
       grind)
    | exact superpose eq651 eq9
    | exact resolve eq9 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq689 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 x
       have i₂ := eq651 X1 x X0
       grind)
    | exact superpose eq651 eq64
    | exact resolve eq64 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq651
  have eq719 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) = (M.op X2 (M.op X2 (M.op X0 (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq678 X0 X1 X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq678
    | exact resolve eq678 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq721 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X0) = (M.op X2 (M.op X2 (M.op X0 (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq719 X0 X1 X2
       have i₂ := eq62 X0 X0 X1
       grind)
    | exact superpose eq62 eq719
    | exact resolve eq719 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq724 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) X0)) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq687 X1 (M.op X1 (M.op (M.op X2 X0) X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq687
    | exact resolve eq687 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X1))) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq687 X1 X1
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq687 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq687
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq687 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq734 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq687 X0 (M.op X0 X0)
       have i₂ := eq687 X0 X0
       grind)
    | exact superpose eq687 eq687
    | exact resolve eq687 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (M.op X0 (M.op X0 X1)) X1 X1
       have i₂ := eq687 X0 X1
       grind)
    | exact superpose eq687 eq62
    | exact resolve eq62 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq749 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq741 X1 X0 X2
       have i₂ := eq687 X0 X1
       grind)
    | exact superpose eq687 eq741
    | exact resolve eq741 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq753 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq578 X0
       have i₂ := eq734 X0
       grind)
    | exact superpose eq734 eq578
    | exact resolve eq578 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq754 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq581 X0
       have i₂ := eq734 (σ X0)
       grind)
    | exact superpose eq734 eq581
    | exact resolve eq581 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq759 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq586 X0
       have i₂ := eq734 (τ X0)
       grind)
    | exact superpose eq734 eq586
    | exact resolve eq586 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq763 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X1))) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq730 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq730 X0 X1
       have r₂ := eq12 (M.op X1 (M.op X0 X1)) X1
       grind)
    | (have r₁ := eq730 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq730 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq824 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq734 X0
       have i₂ := eq14 X0 X0
       grind)
    | (have i₁ := eq734 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq734
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq734 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq829 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq734 X0
       grind)
    | exact superpose eq734 eq9
    | exact resolve eq9 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq851 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq824 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq824 X0 X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq824 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq824 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq876 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X1 X0) (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq689 X1 (M.op X1 (M.op X0 X0))
       have i₂ := eq829 X0 X1
       grind)
    | exact superpose eq829 eq689
    | exact resolve eq689 eq829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq903 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op (M.op X3 X0) X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq679 X1 (M.op X2 (M.op (M.op X3 X0) X0)) X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq679
    | exact resolve eq679 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq904 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X3 (M.op X4 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))))) = (M.op X4 (M.op X0 (M.op (M.op X1 X2) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq679 X3 (M.op X4 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))) X4
       have i₂ := eq61 X2 X4 X0 X1
       grind)
    | exact superpose eq61 eq679
    | exact resolve eq679 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq905 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq679 X1 (M.op X2 (M.op X0 X0)) X2
       have i₂ := eq829 X0 X2
       grind)
    | exact superpose eq829 eq679
    | exact resolve eq679 eq829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq906 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq679 X1 (M.op X2 (M.op X2 X0)) X0
       have i₂ := eq687 X2 X0
       grind)
    | exact superpose eq687 eq679
    | exact resolve eq679 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq909 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X3 X1))) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq679 X2 (M.op X3 X1) X3
       have i₂ := eq679 X3 X1 X0
       grind)
    | (have i₁ := eq679 X2 (M.op X3 X1) X3
       have i₂ := eq679 X0 X1 X3
       grind)
    | exact superpose eq679 eq679
    | exact resolve eq679 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq912 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op X1 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq679 X2 X1 X1
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq679 X0 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq679
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq679 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq954 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X3) X3)) = (M.op X3 (M.op X0 (M.op X0 (M.op X1 (M.op (M.op X2 X3) X3))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X3 X3 X1 X2
       have i₂ := eq679 X3 (M.op X1 (M.op (M.op X2 X3) X3)) X0
       grind)
    | (have i₁ := eq61 X3 X3 X1 X2
       have i₂ := eq679 X0 (M.op X1 (M.op (M.op X2 X3) X3)) X3
       grind)
    | exact superpose eq679 eq61
    | exact resolve eq61 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq971 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op X1 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq912 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq912 X0 X1 (M.op X1 (M.op X0 X1))
       have r₂ := eq12 (M.op (M.op X1 (M.op X0 X1)) X1) (M.op X1 (M.op X0 X1))
       grind)
    | (have r₁ := eq912 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq912 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq975 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))) (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op X3 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))))) = (M.op X3 (M.op X0 (M.op (M.op X1 X2) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq672 X0 X1 X2 X3 x
       have i₂ := eq904 X0 X1 X2 x X3
       grind)
    | exact superpose eq904 eq672
    | exact resolve eq672 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672 eq904
  have eq976 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq721 X0 X1 x
       have i₂ := eq903 X0 x X0 X1
       grind)
    | exact superpose eq903 eq721
    | exact resolve eq721 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq977 : ∀ X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X3) X3)) = (M.op X3 (M.op X1 X3)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq954 x X1 X2 X3
       have i₂ := eq903 X3 x X1 X2
       grind)
    | exact superpose eq903 eq954
    | exact resolve eq954 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq989 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq977 X1 x X0
       grind)
    | exact superpose eq977 eq9
    | exact resolve eq9 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq991 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 X1 X2
       have i₂ := eq977 X1 X2 X0
       grind)
    | exact superpose eq977 eq62
    | exact resolve eq62 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq992 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k (M.op X0 (M.op X1 X0)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 X1 x
       have i₂ := eq977 X1 x X0
       grind)
    | exact superpose eq977 eq63
    | (have j0 := eq63 X0 X1 x
       grind)
    | (have r₁ := eq63 (M.op X1 (M.op (M.op x x) x)) (M.op x (M.op X1 x)) x
       have r₂ := eq977 X1 x x
       grind)
    | (have r₁ := eq63 (M.op x (M.op X1 x)) (M.op X1 (M.op (M.op x x) x)) x
       have r₂ := eq977 X1 x x
       grind)
    | exact resolve eq63 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq996 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X1 (M.op X2 X1)) ∨ (M.op (M.op X0 X1) X1) ≠ (M.op X1 X1) ∨ (k X1 (M.op X2 (M.op (M.op X0 X1) X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 X1 X2
       have i₂ := eq977 X2 X0 X1
       grind)
    | exact superpose eq977 eq176
    | (have j0 := eq176 X0 X1 X2
       grind)
    | exact resolve eq176 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq999 : ∀ X0 X1 X2 : G, (k X1 (M.op X1 (M.op X2 X1))) = X1 ∨ (M.op (M.op X0 X1) X1) ≠ X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq637 X0 X1 X2
       have i₂ := eq977 X2 X0 X1
       grind)
    | exact superpose eq977 eq637
    | (have j0 := eq637 X0 X1 X2
       grind)
    | exact resolve eq637 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq1007 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 (M.op X1 X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq724 x X1 x
       have i₂ := eq977 X1 x x
       grind)
    | exact superpose eq977 eq724
    | exact resolve eq724 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq1015 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq903 X0 X1 X2 x
       have i₂ := eq977 X2 x X0
       grind)
    | exact superpose eq977 eq903
    | exact resolve eq903 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq1017 : ∀ X0 X2 X3 : G, (M.op X3 (M.op X2 (M.op X0 X2))) = (M.op (M.op X3 (M.op X2 (M.op X2 (M.op X0 X2)))) (M.op (M.op X2 (M.op X0 X2)) (M.op X3 (M.op X2 (M.op X2 (M.op X0 X2)))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq975 x X2 X3 X3
       have i₂ := eq977 x X2 X3
       grind)
    | exact superpose eq977 eq975
    | exact resolve eq975 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq1020 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) (M.op (M.op X1 X0) X0)) = X0 ∨ (M.op (M.op X1 X0) X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq290 X0 X1
       have i₂ := eq977 X0 X1 X0
       grind)
    | exact superpose eq977 eq290
    | (have j0 := eq290 X0 X1
       grind)
    | exact resolve eq290 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq1056 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq686 X0 X1 x
       have i₂ := eq976 X1 x
       grind)
    | exact superpose eq976 eq686
    | exact resolve eq686 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq1061 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq851 X0 X1
       have i₂ := eq976 X1 X0
       grind)
    | exact superpose eq976 eq851
    | (have j0 := eq851 X0 X1
       grind)
    | exact resolve eq851 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq1062 : ∀ X1 X3 : G, (M.op X3 (M.op X1 X3)) = (M.op X1 (M.op X3 X3)) := by
    intro X1 X3
    first
    | (have i₁ := eq977 X1 x X3
       have i₂ := eq976 X3 x
       grind)
    | exact superpose eq976 eq977
    | exact resolve eq977 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq1077 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) = X0 ∨ (M.op (M.op X1 X0) X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1020 X0 X1
       have i₂ := eq976 X0 X1
       grind)
    | exact superpose eq976 eq1020
    | (have j0 := eq1020 X0 X1
       grind)
    | exact resolve eq1020 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1080 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1007 X0 X1
       have i₂ := eq976 (M.op X1 X0) X0
       grind)
    | exact superpose eq976 eq1007
    | exact resolve eq1007 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1085 : ∀ X1 X2 : G, (M.op X1 X1) ≠ X1 ∨ (k X1 (M.op X1 (M.op X2 X1))) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq999 x X1 X2
       have i₂ := eq976 X1 x
       grind)
    | exact superpose eq976 eq999
    | (have j0 := eq999 x X1 X2
       grind)
    | exact resolve eq999 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999
  have eq1088 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X1 (M.op X2 X1)) ∨ (k X1 (M.op X2 (M.op (M.op X0 X1) X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq996 X0 X1 X2
       grind)
    | (have r₁ := eq996 X1 X0 X2
       have r₂ := eq976 X0 X1
       grind)
    | exact resolve eq996 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq1091 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq991 X0 X1 x
       have i₂ := eq976 X0 x
       grind)
    | exact superpose eq976 eq991
    | exact resolve eq991 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq1097 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1077 X0 x
       have i₂ := eq976 X0 x
       grind)
    | exact superpose eq976 eq1077
    | (have j0 := eq1077 X0 x
       grind)
    | exact resolve eq1077 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1109 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X1 (M.op X2 X1)) ∨ (k X1 (M.op X2 (M.op (M.op X0 X1) X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1088 X0 X1 X2
       have i₂ := eq976 X1 X0
       grind)
    | exact superpose eq976 eq1088
    | (have j0 := eq1088 X0 X1 X2
       grind)
    | exact resolve eq1088 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq1117 : ∀ X1 X2 : G, (k X1 (M.op X2 (M.op X1 X1))) = X1 ∨ (M.op X1 X1) = (M.op X1 (M.op X2 X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq1109 x X1 X2
       have i₂ := eq976 X1 x
       grind)
    | exact superpose eq976 eq1109
    | (have j0 := eq1109 x X1 X2
       grind)
    | exact resolve eq1109 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109
  have eq1127 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq989 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq989 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq989
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq989 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1145 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1127 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq1127 X1 X1
       have r₂ := eq12 (M.op X1 (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq1127 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1127 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq1148 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq976 (M.op X1 (M.op X0 X0)) X1
       have i₂ := eq829 X0 X1
       grind)
    | exact superpose eq829 eq976
    | exact resolve eq976 eq829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1158 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq625 X0 (M.op X1 X0)
       have i₂ := eq976 X0 X1
       grind)
    | exact superpose eq976 eq625
    | (have j0 := eq625 X0 X0
       grind)
    | exact resolve eq625 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1176 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1148 X0 X1
       have i₂ := eq1080 (M.op X0 X0) X1
       grind)
    | exact superpose eq1080 eq1148
    | exact resolve eq1148 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148
  have eq1205 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1091 (M.op X0 (M.op X1 X0)) X1
       have i₂ := eq989 X0 X1
       grind)
    | exact superpose eq989 eq1091
    | exact resolve eq1091 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1223 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq989 X0 (M.op X0 (M.op X1 X0))
       have i₂ := eq1091 X0 X1
       grind)
    | exact superpose eq1091 eq989
    | exact resolve eq989 eq1091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1234 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1205 X0 X1
       have i₂ := eq1091 X0 X1
       grind)
    | exact superpose eq1091 eq1205
    | exact resolve eq1205 eq1091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091 eq1205
  have eq1243 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1234 X0 X1
       have i₂ := eq1080 (M.op X1 X0) X0
       grind)
    | exact superpose eq1080 eq1234
    | exact resolve eq1234 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234
  have eq1246 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) = (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1243 X0 X1
       have i₂ := eq1062 X0 (M.op X1 X0)
       grind)
    | exact superpose eq1062 eq1243
    | exact resolve eq1243 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243
  have eq1248 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1246 X0 X1
       have i₂ := eq1080 X0 X1
       grind)
    | exact superpose eq1080 eq1246
    | exact resolve eq1246 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246
  have eq1264 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 (M.op X0 X1))
       have i₂ := eq1056 X0 X1
       grind)
    | exact superpose eq1056 eq12
    | exact resolve eq12 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1266 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq625 X0 (M.op X1 (M.op X1 X0))
       have i₂ := eq1056 X1 X0
       grind)
    | exact superpose eq1056 eq625
    | (have j0 := eq625 X0 X0
       grind)
    | exact resolve eq625 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq1272 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq989 X0 (M.op X1 (M.op X1 X0))
       have i₂ := eq1056 X1 X0
       grind)
    | exact superpose eq1056 eq989
    | exact resolve eq989 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1432 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X2 X0)) = (M.op X0 (M.op X3 (M.op X3 (M.op X2 (M.op X2 X0))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq749 (M.op X2 (M.op X2 X0)) X3 (M.op x X0)
       have i₂ := eq749 X0 X2 x
       grind)
    | exact superpose eq749 eq749
    | exact resolve eq749 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1437 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (M.op (M.op X2 (M.op X3 X1)) (M.op X3 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq749 (M.op X3 X1) X3 X2
       have i₂ := eq679 X3 X1 X0
       grind)
    | (have i₁ := eq749 (M.op X3 X1) X3 X2
       have i₂ := eq679 X0 X1 X3
       grind)
    | exact superpose eq679 eq749
    | exact resolve eq749 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1439 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X1 (M.op X0 X1))) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq749 X1 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq749 X0 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq749
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq749 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1459 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ X0 ∨ (k (M.op X2 (M.op X2 X0)) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op X1 X0)) (M.op X2 X0)
       have i₂ := eq749 X0 X1 X2
       grind)
    | exact superpose eq749 eq12
    | exact resolve eq12 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1493 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X1 (M.op X0 X1))) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1439 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1439 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1439 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq1521 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0))) = (M.op X1 (M.op X0 (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1062 X1 (M.op X0 X0)
       have i₂ := eq1062 (M.op X0 X0) X0
       grind)
    | exact superpose eq1062 eq1062
    | exact resolve eq1062 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1522 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X1 (M.op X2 X1)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1062 X2 X1
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq1062 X1 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq1062
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq1062 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1533 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X1 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq679 X2 (M.op X0 X1) X1
       have i₂ := eq1062 X0 X1
       grind)
    | (have i₁ := eq679 X0 (M.op x x) X1
       have i₂ := eq1062 X1 x
       grind)
    | exact superpose eq1062 eq679
    | exact resolve eq679 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1596 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X1 (M.op X2 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1522 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1522 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1522 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1522
  have eq1597 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0))) = (M.op X1 (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1521 X0 X1
       have i₂ := eq976 X0 X0
       grind)
    | exact superpose eq976 eq1521
    | exact resolve eq1521 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521
  have eq1620 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = (M.op X1 (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1597 X0 X1
       have i₂ := eq1176 X0 X1
       grind)
    | exact superpose eq1176 eq1597
    | exact resolve eq1597 eq1176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176 eq1597
  have eq1716 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1223 (M.op X0 X0) X1
       have i₂ := eq1062 X1 X0
       grind)
    | (have i₁ := eq1223 (M.op X1 x) x
       have i₂ := eq1062 X1 x
       grind)
    | exact superpose eq1062 eq1223
    | exact resolve eq1223 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq1786 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1716 X0 X1
       have i₂ := eq1620 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0)))
       grind)
    | exact superpose eq1620 eq1716
    | exact resolve eq1716 eq1620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1620 eq1716
  have eq1803 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0))) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1786 X0 X1
       have i₂ := eq1062 (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0))) (M.op X0 X0)
       grind)
    | exact superpose eq1062 eq1786
    | exact resolve eq1786 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786
  have eq1817 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1803 X0 X1
       have i₂ := eq905 X0 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0)))
       grind)
    | exact superpose eq905 eq1803
    | exact resolve eq1803 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803
  have eq1827 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 (M.op X1 X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1817 X0 X1
       have i₂ := eq1248 X0 X1
       grind)
    | exact superpose eq1248 eq1817
    | exact resolve eq1817 eq1248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248 eq1817
  have eq1981 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq906 X2 X1 X1
       have i₂ := eq679 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq906 X2 X1 X1
       have i₂ := eq679 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq679 eq906
    | exact resolve eq906 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2037 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X0)) = (M.op X1 (M.op X1 (M.op X2 (M.op X3 (M.op X3 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq679 X1 (M.op X2 (M.op X3 (M.op X3 X0))) X2
       have i₂ := eq906 X0 X2 X3
       grind)
    | exact superpose eq906 eq679
    | exact resolve eq679 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2225 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X3 (M.op X1 (M.op X0 X1))))) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq679 X2 (M.op X3 (M.op X1 (M.op X0 X1))) X3
       have i₂ := eq1015 X1 X3 X0
       grind)
    | exact superpose eq1015 eq679
    | exact resolve eq679 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2228 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X3 (M.op X3 (M.op X2 (M.op X1 (M.op X0 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq749 (M.op X2 (M.op X1 (M.op X0 X1))) X3 X2
       have i₂ := eq1015 X1 X2 X0
       grind)
    | exact superpose eq1015 eq749
    | exact resolve eq749 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2245 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2228 X0 X1 X2 x
       have i₂ := eq2225 X0 X1 x X2
       grind)
    | exact superpose eq2225 eq2228
    | exact resolve eq2228 eq2225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2225 eq2228
  have eq2281 : ∀ X0 X2 X3 : G, (M.op X3 (M.op X2 (M.op X0 X2))) = (M.op (M.op X2 (M.op X0 X2)) (M.op (M.op X2 (M.op X2 (M.op X0 X2))) (M.op X3 (M.op X2 (M.op X2 (M.op X0 X2)))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1017 X0 X2 X3
       have i₂ := eq2245 X3 (M.op X2 (M.op X2 (M.op X0 X2))) (M.op X2 (M.op X0 X2))
       grind)
    | exact superpose eq2245 eq1017
    | exact resolve eq1017 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017
  have eq2298 : ∀ X0 X2 X3 : G, (M.op X3 (M.op X2 (M.op X0 X2))) = (M.op (M.op X2 (M.op X0 X2)) (M.op X3 (M.op (M.op X2 (M.op X0 X2)) (M.op X2 (M.op X2 (M.op X0 X2)))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2281 X0 X2 X3
       have i₂ := eq2245 X2 (M.op X2 (M.op X0 X2)) X3
       grind)
    | exact superpose eq2245 eq2281
    | exact resolve eq2281 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2281
  have eq2311 : ∀ X0 X2 X3 : G, (M.op X3 (M.op X2 (M.op X0 X2))) = (M.op (M.op X2 (M.op X0 X2)) (M.op X3 (M.op X2 (M.op (M.op X2 (M.op X0 X2)) (M.op X2 (M.op X0 X2)))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2298 X0 X2 X3
       have i₂ := eq1062 X2 (M.op X2 (M.op X0 X2))
       grind)
    | exact superpose eq1062 eq2298
    | exact resolve eq2298 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2298
  have eq2320 : ∀ X0 X2 X3 : G, (M.op X3 (M.op X2 (M.op X0 X2))) = (M.op (M.op X2 (M.op X0 X2)) (M.op X3 (M.op X2 (M.op (M.op X0 X2) (M.op X2 (M.op X0 X2)))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2311 X0 X2 X3
       have i₂ := eq1080 (M.op X0 X2) X2
       grind)
    | exact superpose eq1080 eq2311
    | exact resolve eq2311 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2311
  have eq2328 : ∀ X0 X2 X3 : G, (M.op X3 (M.op X2 (M.op X0 X2))) = (M.op (M.op X2 (M.op X0 X2)) (M.op X3 (M.op X0 X2))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2320 X0 X2 X3
       have i₂ := eq989 (M.op X0 X2) X2
       grind)
    | exact superpose eq989 eq2320
    | exact resolve eq2320 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2320
  have eq2423 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 X0))) = (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op X1 (M.op X2 (M.op X2 X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1272 (M.op X1 (M.op X2 (M.op X2 X0))) X1
       have i₂ := eq906 X0 X1 X2
       grind)
    | exact superpose eq906 eq1272
    | exact resolve eq1272 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2461 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X2 X1)) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1272 X1 X2
       have i₂ := eq679 X1 X1 X0
       grind)
    | (have i₁ := eq1272 X1 X2
       have i₂ := eq679 X0 X1 X1
       grind)
    | exact superpose eq679 eq1272
    | exact resolve eq1272 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272
  have eq2540 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))) = (M.op X1 (M.op X2 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2423 X0 X1 X2
       have i₂ := eq2037 X0 (M.op X1 (M.op X2 (M.op X2 X0))) X1 X2
       grind)
    | exact superpose eq2037 eq2423
    | exact resolve eq2423 eq2037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2037 eq2423
  have eq2566 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0))) = (M.op X1 (M.op X2 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2540 X0 X1 X2
       have i₂ := eq1080 (M.op X0 X0) X1
       grind)
    | exact superpose eq1080 eq2540
    | exact resolve eq2540 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2540
  have eq2585 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 X0))) = (M.op X1 (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2566 X0 X1 X2
       have i₂ := eq2245 X0 X0 X1
       grind)
    | exact superpose eq2245 eq2566
    | exact resolve eq2566 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2566
  have eq3116 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op X1 (M.op X2 (M.op X2 X0)))) = (M.op (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op X0 X0))) (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1827 (M.op X1 (M.op X2 (M.op X2 X0))) X1
       have i₂ := eq906 X0 X1 X2
       grind)
    | exact superpose eq906 eq1827
    | exact resolve eq1827 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1827
  have eq3213 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op X1 (M.op X2 (M.op X2 X0)))) = (M.op X0 (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3116 X0 X1 X2
       have i₂ := eq829 X0 (M.op X1 (M.op X2 (M.op X2 X0)))
       grind)
    | exact superpose eq829 eq3116
    | exact resolve eq3116 eq829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3116
  have eq3239 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X2 X0)) (M.op X1 (M.op X2 (M.op X2 X0)))) = (M.op X0 (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3213 X0 X1 X2
       have i₂ := eq1080 (M.op X2 (M.op X2 X0)) X1
       grind)
    | exact superpose eq1080 eq3213
    | exact resolve eq3213 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3213
  have eq3251 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X2 (M.op X2 X0)))) = (M.op X0 (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3239 X0 X1 X2
       have i₂ := eq2245 X2 (M.op X2 X0) X1
       grind)
    | exact superpose eq2245 eq3239
    | exact resolve eq3239 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3239
  have eq3259 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X2 X0) (M.op X2 X0)))) = (M.op X0 (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3251 X0 X1 X2
       have i₂ := eq1062 X2 (M.op X2 X0)
       grind)
    | exact superpose eq1062 eq3251
    | exact resolve eq3251 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3251
  have eq3265 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 (M.op X2 X0)))) = (M.op X0 (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3259 X0 X1 X2
       have i₂ := eq1080 X0 X2
       grind)
    | exact superpose eq1080 eq3259
    | exact resolve eq3259 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3259
  have eq3269 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3265 X0 X1 X2
       have i₂ := eq989 X0 X2
       grind)
    | exact superpose eq989 eq3265
    | exact resolve eq3265 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3265
  have eq3305 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 X0))) = (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1981 X2 X1 (M.op X1 (M.op X2 X0))
       have i₂ := eq1981 X1 X2 X0
       grind)
    | exact superpose eq1981 eq1981
    | exact resolve eq1981 eq1981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3336 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X0 X2)))) ≠ X3 ∨ (M.op X3 X2) = (k X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq566 X3 X2
       have i₂ := eq1981 X1 X0 X2
       grind)
    | exact superpose eq1981 eq566
    | (have j0 := eq566 X3 X2
       grind)
    | (have r₁ := eq566 (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) X2
       have r₂ := eq1981 X0 X1 X2
       grind)
    | exact resolve eq566 eq1981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq3339 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X1 (M.op X1 (M.op X0 X2)))))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq829 X2 X3
       have i₂ := eq1981 X1 X0 X2
       grind)
    | exact superpose eq1981 eq829
    | exact resolve eq829 eq1981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3449 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 X0))) = (M.op (M.op X2 X0) (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3305 X0 X1 X2
       have i₂ := eq1080 (M.op X2 X0) X1
       grind)
    | exact superpose eq1080 eq3305
    | exact resolve eq3305 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3305
  have eq3500 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 X0))) = (M.op X1 (M.op X0 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3449 X0 X1 X2
       have i₂ := eq2245 X2 X0 X1
       grind)
    | exact superpose eq2245 eq3449
    | exact resolve eq3449 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3449
  have eq3931 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = X1 ∨ (k X1 X2) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1145 X1 X2
       have i₂ := eq679 X1 X1 X0
       grind)
    | (have i₁ := eq1145 X1 X2
       have i₂ := eq679 X0 X1 X1
       grind)
    | exact superpose eq679 eq1145
    | (have j0 := eq1145 X1 X2
       grind)
    | exact resolve eq1145 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145
  have eq4752 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op X2 (M.op X2 (M.op X3 (M.op X0 (M.op X1 X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq679 X2 (M.op X3 (M.op X0 (M.op X1 X1))) X3
       have i₂ := eq905 X1 X3 X0
       grind)
    | exact superpose eq905 eq679
    | exact resolve eq679 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4757 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X2 (M.op X0 X1)))) = (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X2 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq906 (M.op X2 (M.op X0 (M.op X1 X1))) X3 X2
       have i₂ := eq905 X1 X2 X0
       grind)
    | exact superpose eq905 eq906
    | exact resolve eq906 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4796 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X2 (M.op X0 X1)))) = (M.op (M.op X0 (M.op X1 X1)) (M.op X2 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4757 X0 X1 X2 X3
       have i₂ := eq1080 (M.op X0 (M.op X1 X1)) X2
       grind)
    | exact superpose eq1080 eq4757
    | exact resolve eq4757 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4757
  have eq4866 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X2 (M.op X0 X1)))) = (M.op X2 (M.op (M.op X1 X1) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4796 X0 X1 X2 X3
       have i₂ := eq2245 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq2245 eq4796
    | exact resolve eq4796 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4796
  have eq4915 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X2 (M.op X0 X1)))) = (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4866 X0 X1 X2 X3
       have i₂ := eq2245 X1 X1 X0
       grind)
    | exact superpose eq2245 eq4866
    | exact resolve eq4866 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2245 eq4866
  have eq6254 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq1061 (σ X0) X1
       grind)
    | exact superpose eq1061 eq22
    | (have j1 := eq1061 (σ X0) X1
       grind)
    | exact resolve eq22 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6262 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1061 (σ X0) (σ X1)
       grind)
    | exact superpose eq1061 eq15
    | (have j1 := eq1061 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6269 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X1) (τ X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq1061 (τ X0) (τ X1)
       grind)
    | exact superpose eq1061 eq31
    | (have j1 := eq1061 (τ X0) (τ X1)
       grind)
    | exact resolve eq31 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061
  have eq6709 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X0 (M.op X4 (M.op X4 X2))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq909 X4 X2 x X0
       have i₂ := eq909 X1 X2 x X0
       grind)
    | (have i₁ := eq909 X0 X1 X0 X0
       have i₂ := eq909 X0 X1 X2 X0
       grind)
    | exact superpose eq909 eq909
    | exact resolve eq909 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6999 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X3 X2)) (M.op X3 (M.op X3 X2))) = (M.op X1 (M.op X4 (M.op X4 (M.op X0 (M.op X0 (M.op X1 X2)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1981 X4 X1 (M.op X3 (M.op X3 X2))
       have i₂ := eq909 X3 X2 X0 X1
       grind)
    | (have i₁ := eq1981 X0 X2 (M.op X2 (M.op X3 X1))
       have i₂ := eq909 X0 X1 X2 X3
       grind)
    | exact superpose eq909 eq1981
    | exact resolve eq1981 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7037 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X4 (M.op X4 (M.op X0 (M.op X0 (M.op X1 X2)))))) = X2 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq6999 X0 X1 X2 x X4
       have i₂ := eq2461 x X2 x
       grind)
    | exact superpose eq2461 eq6999
    | exact resolve eq6999 eq2461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6999
  have eq17612 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 (M.op X1 (M.op X0 (M.op X2 X3)))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3339 X2 X0 X3 X2
       have i₂ := eq909 X1 (M.op X0 (M.op X2 X3)) X2 X0
       grind)
    | (have i₁ := eq3339 X0 X0 X2 X3
       have i₂ := eq909 X0 (M.op X0 (M.op X0 X2)) X2 X3
       grind)
    | exact superpose eq909 eq3339
    | exact resolve eq3339 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3339
  have eq25329 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X0
       have i₂ := eq605 X1 (τ X0)
       grind)
    | exact superpose eq605 eq31
    | (have j1 := eq605 X1 (τ X0)
       grind)
    | exact resolve eq31 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25334 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq605 X1 (τ X0)
       grind)
    | exact superpose eq605 eq17
    | (have j1 := eq605 X1 (τ X0)
       grind)
    | exact resolve eq17 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq25349 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq25334 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq25334
    | (have j0 := eq25334 X0 X1
       grind)
    | exact resolve eq25334 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25334
  have eq25354 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25329 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25329
    | (have j0 := eq25329 X0 X1
       grind)
    | exact resolve eq25329 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25329
  have eq25380 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq25349 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25349
    | (have j0 := eq25349 X0 X1
       grind)
    | exact resolve eq25349 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25349
  have eq25397 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X0))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25380 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25380
    | (have j0 := eq25380 X0 X1
       grind)
    | exact resolve eq25380 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25380
  have eq25474 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25397 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25397
    | (have j0 := eq25397 X1 (σ X0)
       grind)
    | exact resolve eq25397 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25487 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X1) (τ X0))
       have i₂ := eq25397 X0 X1
       grind)
    | exact superpose eq25397 eq10
    | (have j1 := eq25397 X0 X1
       grind)
    | exact resolve eq10 eq25397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25397
  have eq25499 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (M.op X0 (τ X1)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25487 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25487
    | (have j0 := eq25487 X1 (σ X0)
       grind)
    | exact resolve eq25487 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25487
  have eq25623 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op X0 (τ X1)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25499 X0 X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq25499
    | (have j0 := eq25499 X0 X1
       grind)
    | exact resolve eq25499 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25499
  have eq25662 : ∀ X0 : G, (τ (M.op (σ (τ X0)) (σ (τ X0)))) = (M.op (τ (M.op (σ (τ X0)) (σ (τ X0)))) (τ X0)) ∨ (k X0 (σ (τ (M.op (σ (τ X0)) (σ (τ X0)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq754 (τ X0)
       have i₂ := eq25623 (τ (M.op (σ (τ X0)) (σ (τ X0)))) X0
       grind)
    | exact superpose eq25623 eq754
    | (have j1 := eq25623 (τ (M.op (σ (τ X0)) (σ (τ X0)))) X0
       grind)
    | exact resolve eq754 eq25623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25623
  have eq25667 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (k X0 (σ (τ (M.op (σ (τ X0)) (σ (τ X0)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq25662 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25662
    | (have j0 := eq25662 X0
       grind)
    | exact resolve eq25662 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25662
  have eq25695 : ∀ X0 : G, (k X0 (M.op (σ (τ X0)) (σ (τ X0)))) = X0 ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq25667 X0
       have i₂ := eq11 (M.op (σ (τ X0)) (σ (τ X0)))
       grind)
    | exact superpose eq11 eq25667
    | (have j0 := eq25667 X0
       grind)
    | exact resolve eq25667 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25667
  have eq25704 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq25695 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25695
    | (have j0 := eq25695 X0
       grind)
    | exact resolve eq25695 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25695
  have eq25706 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25704 X0
       have i₂ := eq753 X0
       grind)
    | exact superpose eq753 eq25704
    | (have j0 := eq25704 X0
       grind)
    | exact resolve eq25704 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25704
  have eq27204 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))) ≠ X2 ∨ (k (M.op X2 (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2))))) (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1097 X0
       have i₂ := eq906 X0 X1 X2
       grind)
    | exact superpose eq906 eq1097
    | exact resolve eq1097 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27218 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X1 X2)) (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2))))) = X2 ∨ (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))) ≠ X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27204 X0 X1 X2
       have i₂ := eq1432 X2 X1 X0
       grind)
    | exact superpose eq1432 eq27204
    | (have j0 := eq27204 X0 X1 X2
       grind)
    | exact resolve eq27204 eq1432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27204
  have eq27311 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op X2 X1) (M.op (M.op X2 X1) (M.op X0 (M.op X0 X1)))) ∨ (M.op X0 (M.op X0 X1)) = (k (M.op X2 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq763 X0 (M.op X0 X1)
       have i₂ := eq679 X0 X1 x
       grind)
    | (have i₁ := eq763 x (M.op x X1)
       have i₂ := eq679 X0 X1 x
       grind)
    | exact superpose eq679 eq763
    | exact resolve eq763 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq27597 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X0 (M.op X0 (M.op X1 (M.op X1 X1)))) ∨ (M.op X0 (M.op X0 X1)) = (k (M.op X2 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27311 X0 X1 X2
       have i₂ := eq4915 X0 X1 X0 (M.op X2 X1)
       grind)
    | (have i₁ := eq27311 X1 X1 X2
       have i₂ := eq4915 (M.op X2 X1) X1 (M.op X2 X1) x
       grind)
    | exact superpose eq4915 eq27311
    | (have j0 := eq27311 X0 X1 X2
       grind)
    | exact resolve eq27311 eq4915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4915 eq27311
  have eq27645 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 X1) ∨ (M.op X0 (M.op X0 X1)) = (k (M.op X2 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27597 X0 X1 X2
       have i₂ := eq905 X1 X0 X1
       grind)
    | exact superpose eq905 eq27597
    | (have j0 := eq27597 X0 X1 X2
       grind)
    | exact resolve eq27597 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27597
  have eq29130 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25474 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25474
    | (have j0 := eq25474 X1 (σ X0)
       grind)
    | exact resolve eq25474 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25474
  have eq29171 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29130 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq29130
    | (have j0 := eq29130 X0 X1
       grind)
    | exact resolve eq29130 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29130
  have eq29177 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29171 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq29171
    | (have j0 := eq29171 X0 X1
       grind)
    | exact resolve eq29171 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29171
  have eq29229 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))) ≠ X2 ∨ (k (M.op X3 (M.op X3 X2)) (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2))))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1459 X0 X0 X2
       have i₂ := eq906 X0 X1 X2
       grind)
    | exact superpose eq906 eq1459
    | exact resolve eq1459 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1459
  have eq29503 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X0))) ≠ X0 ∨ (M.op X2 (M.op X0 (M.op X1 X0))) = X2 ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X0 (M.op X1 X0)) X2) ∨ (k (M.op X0 (M.op X1 X0)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq569 X1 (M.op X0 (M.op X1 X0)) X2
       have i₂ := eq989 X0 X1
       grind)
    | exact superpose eq989 eq569
    | (have j0 := eq569 X0 (M.op X0 (M.op X1 X0)) X2
       grind)
    | exact resolve eq569 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq30914 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29177 X0 X1
       have i₂ := eq591 X0 X1
       grind)
    | exact superpose eq591 eq29177
    | (have j0 := eq29177 X1 X0
       have j1 := eq591 X1 X0
       grind)
    | exact resolve eq29177 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29177
  have eq30929 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq591 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq30933 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq30914 X0 X1
       have j1 := eq30929 X1 X0
       grind)
    | (have r₁ := eq30914 X1 X0
       have r₂ := eq30929 X0 X1
       grind)
    | exact resolve eq30914 eq30929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30914 eq30929
  have eq31087 : ∀ X0 : G, (τ X0) = (τ (M.op (σ (τ X0)) (σ (τ X0)))) ∨ (k X0 (σ (τ (M.op (σ (τ X0)) (σ (τ X0)))))) = (σ (M.op (τ (M.op (σ (τ X0)) (σ (τ X0)))) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq754 (τ X0)
       have i₂ := eq616 (τ (M.op (σ (τ X0)) (σ (τ X0)))) X0
       grind)
    | exact superpose eq616 eq754
    | (have j1 := eq616 (τ (M.op (σ (τ X0)) (σ (τ X0)))) X0
       grind)
    | exact resolve eq754 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616 eq754
  have eq31092 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (σ (τ (M.op (σ (τ X0)) (σ (τ X0)))))) = (σ (M.op (τ (M.op (σ (τ X0)) (σ (τ X0)))) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq31087 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31087
    | (have j0 := eq31087 X0
       grind)
    | exact resolve eq31087 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31087
  have eq31129 : ∀ X0 : G, (k X0 (σ (τ (M.op X0 X0)))) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31092 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31092
    | (have j0 := eq31092 X0
       grind)
    | exact resolve eq31092 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31092
  have eq31138 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31129 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq31129
    | (have j0 := eq31129 X0
       grind)
    | exact resolve eq31129 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31129
  have eq31144 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31138 X0
       have i₂ := eq753 X0
       grind)
    | exact superpose eq753 eq31138
    | (have j0 := eq31138 X0
       grind)
    | exact resolve eq31138 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31138
  have eq54050 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X0 (M.op X1 (M.op X1 (M.op X2 X2)))))) = X2 ∨ (M.op X2 X2) = (M.op X2 (M.op (M.op X2 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1117 X2 (M.op X2 X2)
       have i₂ := eq906 (M.op X2 X2) X0 X1
       grind)
    | exact superpose eq906 eq1117
    | (have j0 := eq1117 X2 (M.op X2 X2)
       grind)
    | exact resolve eq1117 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906 eq1117
  have eq54130 : ∀ X1 X2 : G, (k X2 (M.op X1 (M.op X1 X2))) = X2 ∨ (M.op X2 X2) = (M.op X2 (M.op (M.op X2 X2) X2)) := by
    intro X1 X2
    first
    | (have i₁ := eq54050 x X1 X2
       have i₂ := eq4752 X1 X2 x X1
       grind)
    | exact superpose eq4752 eq54050
    | (have j0 := eq54050 x X1 X2
       grind)
    | exact resolve eq54050 eq4752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4752 eq54050
  have eq54199 : ∀ X1 X2 : G, (M.op X2 X2) = (M.op X2 (M.op X2 X2)) ∨ (k X2 (M.op X1 (M.op X1 X2))) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq54130 X1 X2
       have i₂ := eq976 X2 X2
       grind)
    | exact superpose eq976 eq54130
    | (have j0 := eq54130 X1 X2
       grind)
    | exact resolve eq54130 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54130
  have eq80658 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq976 (τ X0) (τ (M.op X0 X0))
       have i₂ := eq25706 X0
       grind)
    | exact superpose eq25706 eq976
    | (have j1 := eq25706 X0
       grind)
    | exact resolve eq976 eq25706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80732 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op X1 (M.op X1 (M.op X2 (M.op X2 (τ (M.op X0 X0))))))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7037 X2 (τ (M.op X0 X0)) (τ X0) X1
       have i₂ := eq25706 X0
       grind)
    | exact superpose eq25706 eq7037
    | (have j1 := eq25706 X0
       grind)
    | exact resolve eq7037 eq25706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7037 eq25706
  have eq80749 : ∀ X0 X2 : G, (τ X0) = (M.op X2 (M.op X2 (τ (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq80732 X0 x X2
       have i₂ := eq1432 (τ (M.op X0 X0)) X2 x
       grind)
    | exact superpose eq1432 eq80732
    | (have j0 := eq80732 X0 x X2
       grind)
    | exact resolve eq80732 eq1432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80732
  have eq82067 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (τ X0))) = (τ (M.op X1 (M.op X1 X0))) ∨ (M.op X1 (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80749 (M.op X0 (M.op X0 X1)) X2
       have i₂ := eq2461 X0 X1 X0
       grind)
    | exact superpose eq2461 eq80749
    | exact resolve eq80749 eq2461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80749
  have eq82556 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq30933 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq30933
    | (have j0 := eq30933 (τ X1) (τ X0)
       grind)
    | exact resolve eq30933 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82583 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq30933 X1 X0
       grind)
    | exact superpose eq30933 eq10
    | (have j1 := eq30933 X1 X0
       grind)
    | exact resolve eq10 eq30933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30933
  have eq82604 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq82583 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq82583
    | (have j0 := eq82583 X0 X1
       grind)
    | exact resolve eq82583 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82583
  have eq82625 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (σ (M.op (τ X1) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq82556 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq82556
    | (have j0 := eq82556 X0 X1
       grind)
    | exact resolve eq82556 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82556
  have eq82654 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ (M.op (τ X1) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq82625 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82625
    | (have j0 := eq82625 X0 X1
       grind)
    | exact resolve eq82625 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82625
  have eq82665 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq82654 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82654
    | (have j0 := eq82654 X0 X1
       grind)
    | exact resolve eq82654 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82654
  have eq82671 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq82665 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq82665
    | (have j0 := eq82665 X0 X1
       grind)
    | exact resolve eq82665 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82665
  have eq82672 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82604 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82604
    | (have j0 := eq82604 X1 (τ X0)
       grind)
    | exact resolve eq82604 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82716 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82604 y x
       grind)
    | exact superpose eq82604 eq16
    | (have j1 := eq82604 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq82604 y x
       grind)
    | exact resolve eq16 eq82604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82604
  have eq82908 : y = (k y x) := by grind
  clear eq82716
  have eq85600 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (M.op X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X0
       have i₂ := eq82672 X1 (τ X0)
       grind)
    | exact superpose eq82672 eq31
    | (have j1 := eq82672 X1 (τ X0)
       grind)
    | exact resolve eq31 eq82672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82672
  have eq85627 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85600 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq85600
    | (have j0 := eq85600 X0 X1
       grind)
    | exact resolve eq85600 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85600
  have eq103940 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (τ X1) = (τ (k X1 X0)) ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25354 X1 X0
       have i₂ := eq85627 X1 X0
       grind)
    | exact superpose eq85627 eq25354
    | (have j0 := eq25354 X1 X0
       have j1 := eq85627 X1 X0
       grind)
    | exact resolve eq25354 eq85627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25354 eq85627
  have eq103975 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq103940 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103940
  have eq104024 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq103975 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq103975
    | exact resolve eq103975 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103975
  have eq104135 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq104024 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq104024
    | (have j0 := eq104024 X0 X1
       grind)
    | exact resolve eq104024 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104024
  have eq104142 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq104135 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq104135
    | (have j0 := eq104135 X0 X1
       grind)
    | exact resolve eq104135 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104135
  have eq104330 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq104142 X0 (M.op X0 X0)
       have i₂ := eq753 X0
       grind)
    | exact superpose eq753 eq104142
    | exact resolve eq104142 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104393 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq104142 X1 X0
       grind)
    | exact superpose eq104142 eq10
    | (have j1 := eq104142 X1 X0
       grind)
    | exact resolve eq10 eq104142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104142
  have eq109580 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq976 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq104330 X0
       grind)
    | exact superpose eq104330 eq976
    | (have j1 := eq104330 X0
       grind)
    | exact resolve eq976 eq104330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104330
  have eq125761 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X0) (M.op (M.op X1 X0) (M.op X4 (M.op X4 (M.op X0 (M.op X2 X0)))))) = X0 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1437 X0 (M.op X1 (M.op X0 X1)) X2 (M.op X2 X1)
       have i₂ := eq1493 X0 X1 X2
       grind)
    | exact superpose eq1493 eq1437
    | (have j1 := eq1493 X2 X0 X2
       grind)
    | exact resolve eq1437 eq1493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437 eq1493
  have eq125894 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op (M.op X1 X0) (M.op X2 X0))) = X0 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq125761 X0 X1 X2 X3 x
       have i₂ := eq1015 X0 x X2
       grind)
    | exact superpose eq1015 eq125761
    | (have j0 := eq125761 X0 X1 X2 X3 x
       grind)
    | exact resolve eq125761 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015 eq125761
  have eq150137 : ∀ X0 X1 : G, (M.op X1 (k (M.op X0 X1) X0)) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq829 X1 X1
       have i₂ := eq27645 X1 X1 X0
       grind)
    | exact superpose eq27645 eq829
    | (have j1 := eq27645 X0 X1 X0
       grind)
    | exact resolve eq829 eq27645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150176 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X2 (k (M.op X0 X1) X0))) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1981 X2 X2 X1
       have i₂ := eq27645 X2 X1 X0
       grind)
    | exact superpose eq27645 eq1981
    | (have j1 := eq27645 X0 X1 X0
       grind)
    | exact resolve eq1981 eq27645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27645
  have eq155245 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X0 (M.op X1 (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0)))))) ∨ (k X0 (M.op X3 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17612 X1 X2 X0 (M.op X0 X0)
       have i₂ := eq54199 X3 X0
       grind)
    | exact superpose eq54199 eq17612
    | (have j1 := eq54199 X3 X0
       grind)
    | exact resolve eq17612 eq54199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54199
  have eq155343 : ∀ X0 X3 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op X3 (M.op X3 X0))) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq155245 X0 x x X3
       have i₂ := eq17612 x x X0 X0
       grind)
    | exact superpose eq17612 eq155245
    | (have j0 := eq155245 X0 x x X3
       grind)
    | exact resolve eq155245 eq17612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155245
  have eq155869 : ∀ X0 X3 : G, (k X0 (M.op X3 (M.op X3 X0))) = X0 := by
    intro X0 X3
    first
    | (have j0 := eq155343 X0 X3
       have j1 := eq1266 X0 X3
       grind)
    | (have r₁ := eq155343 X0 X3
       have r₂ := eq1266 X0 x
       grind)
    | exact resolve eq155343 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266 eq155343
  have eq156239 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1264 X0 X1
       have i₂ := eq155869 X0 X1
       grind)
    | exact superpose eq155869 eq1264
    | (have j0 := eq1264 X0 X1
       grind)
    | exact resolve eq1264 eq155869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264
  have eq156249 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))) ≠ X2 ∨ (M.op X1 (M.op X1 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27218 X0 X1 X2
       have i₂ := eq155869 (M.op X1 (M.op X1 X2)) X0
       grind)
    | exact superpose eq155869 eq27218
    | (have j0 := eq27218 X0 X1 X2
       grind)
    | exact resolve eq27218 eq155869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27218
  have eq156604 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (k (M.op X3 (M.op X3 X2)) (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq155869 (M.op X3 (M.op X3 X2)) X0
       have i₂ := eq6709 X0 X3 X2 X1
       grind)
    | (have i₁ := eq155869 (M.op X3 (M.op X3 X2)) X0
       have i₂ := eq6709 X0 X1 X2 X3
       grind)
    | exact superpose eq6709 eq155869
    | exact resolve eq155869 eq6709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6709
  have eq156789 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k (M.op X1 (M.op X1 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq155869 (M.op X1 (M.op X1 X0)) X0
       have i₂ := eq3269 X0 X0 X1
       grind)
    | exact superpose eq3269 eq155869
    | exact resolve eq155869 eq3269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156861 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op X1 (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 (M.op X1 (τ X0)))
       have i₂ := eq155869 (τ X0) X1
       grind)
    | exact superpose eq155869 eq17
    | exact resolve eq17 eq155869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq156881 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 (M.op X1 (τ X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq156861 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq156861
    | exact resolve eq156861 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156861
  have eq156939 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1097 X0
       have i₂ := eq156789 X0 X0
       grind)
    | exact superpose eq156789 eq1097
    | (have j0 := eq1097 X0
       grind)
    | exact resolve eq1097 eq156789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097 eq156789
  have eq157071 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))) ≠ X2 ∨ (M.op X3 (M.op X3 X2)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq29229 X0 X1 X2 X3
       have i₂ := eq156604 X0 X1 X2 X3
       grind)
    | exact superpose eq156604 eq29229
    | (have j0 := eq29229 X0 X1 X2 X3
       grind)
    | exact resolve eq29229 eq156604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29229 eq156604
  have eq157744 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ X0 ∨ (M.op X1 (M.op X1 X0)) = (M.op (M.op X1 (M.op X1 X0)) X0) ∨ (M.op (M.op X1 (M.op X1 X0)) X0) = (k X0 (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq156939 (M.op X0 (M.op X0 X1))
       have i₂ := eq3931 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq3931 eq156939
    | (have j1 := eq3931 X0 X0 (M.op X1 (M.op X1 X0))
       grind)
    | exact resolve eq156939 eq3931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3931 eq156939
  have eq157794 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ X0 ∨ (M.op (M.op X1 (M.op X1 X0)) X0) = (k X0 (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq157744 X0 X1
       have j1 := eq12 X0 (M.op X1 (M.op X1 X0))
       grind)
    | (have r₁ := eq157744 X0 X1
       have r₂ := eq12 X0 (M.op X1 (M.op X1 X0))
       grind)
    | exact resolve eq157744 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157744
  have eq157825 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) X0) = X0 ∨ (M.op X1 (M.op X1 X0)) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq157794 X0 X1
       have i₂ := eq155869 X0 X1
       grind)
    | exact superpose eq155869 eq157794
    | (have j0 := eq157794 X0 X1
       grind)
    | exact resolve eq157794 eq155869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157794
  have eq157847 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq157825 X0 X1
       have i₂ := eq1056 X1 X0
       grind)
    | exact superpose eq1056 eq157825
    | (have j0 := eq157825 X0 X1
       grind)
    | exact resolve eq157825 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157825
  have eq158089 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X1 (M.op X1 X1))) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq157847 (M.op X0 X1) X0
       have i₂ := eq2585 X1 X0 X0
       grind)
    | (have i₁ := eq157847 (M.op X0 X0) X0
       have i₂ := eq2585 X0 X0 x
       grind)
    | exact superpose eq2585 eq157847
    | (have j0 := eq157847 (M.op X0 X1) X1
       grind)
    | exact resolve eq157847 eq2585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2585
  have eq158107 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X1 (M.op X1 X0)) = (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq157847 (M.op X1 (M.op X1 X0)) X0
       have i₂ := eq3269 X0 X0 X1
       grind)
    | exact superpose eq3269 eq157847
    | (have j0 := eq157847 (M.op X1 (M.op X1 X0)) X1
       grind)
    | exact resolve eq157847 eq3269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157847
  have eq158180 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X1 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq158107 X0 X1
       have i₂ := eq2461 X1 X0 X1
       grind)
    | exact superpose eq2461 eq158107
    | (have j0 := eq158107 X0 X1
       grind)
    | exact resolve eq158107 eq2461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158107
  have eq158195 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X1 (M.op X1 X1))) ∨ (M.op X0 X1) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq158089 X0 X1
       have i₂ := eq1080 X1 X0
       grind)
    | exact superpose eq1080 eq158089
    | (have j0 := eq158089 X0 X1
       grind)
    | exact resolve eq158089 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158089
  have eq159424 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))) ∨ (M.op X1 (M.op X1 X0)) = (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq156239 (M.op X1 (M.op X1 X0)) X0
       have i₂ := eq3269 X0 X0 X1
       grind)
    | exact superpose eq3269 eq156239
    | (have j0 := eq156239 (M.op X1 (M.op X1 X0)) X1
       grind)
    | exact resolve eq156239 eq3269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3269 eq156239
  have eq159491 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 (M.op X1 X0)) = (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq159424 X0 X1
       have i₂ := eq2461 X1 X0 X1
       grind)
    | exact superpose eq2461 eq159424
    | (have j0 := eq159424 X0 X1
       grind)
    | exact resolve eq159424 eq2461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159424
  have eq159718 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq159491 X0 X1
       have i₂ := eq2461 X1 X0 X1
       grind)
    | exact superpose eq2461 eq159491
    | (have j0 := eq159491 X0 X1
       grind)
    | exact resolve eq159491 eq2461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2461 eq159491
  have eq195587 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6254 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6254
    | exact resolve eq6254 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6254
  have eq197059 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq195587 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq195587
    | (have j0 := eq195587 X0 X1
       grind)
    | exact resolve eq195587 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195587
  have eq197466 : (τ y) = (τ (M.op x y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq197059 x y
       have i₂ := eq82908
       grind)
    | exact superpose eq82908 eq197059
    | (have j0 := eq197059 x y
       grind)
    | exact resolve eq197059 eq82908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197059
  have eq199368 : ∀ X0 : G, (τ (k (M.op x y) X0)) = (k (τ y) (τ X0)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq31 X0 (M.op x y)
       have i₂ := eq197466
       grind)
    | exact superpose eq197466 eq31
    | exact resolve eq31 eq197466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197466
  have eq199459 : ∀ X0 : G, (τ (k (M.op x y) X0)) = (τ (k y X0)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq199368 X0
       have i₂ := eq31 X0 y
       grind)
    | exact superpose eq31 eq199368
    | exact resolve eq199368 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq199368
  have eq242269 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq82671 X0 (M.op X0 X0)
       have i₂ := eq80658 X0
       grind)
    | exact superpose eq80658 eq82671
    | (have j0 := eq82671 X0 (M.op X0 X0)
       have j1 := eq80658 X0
       grind)
    | exact resolve eq82671 eq80658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80658 eq82671
  have eq242630 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq242269 X0
       have j1 := eq1158 X0 X0
       grind)
    | (have r₁ := eq242269 X0
       have r₂ := eq1158 X0 x
       grind)
    | exact resolve eq242269 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242269
  have eq242730 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq242630 X0
       have i₂ := eq976 X0 X0
       grind)
    | exact superpose eq976 eq242630
    | (have j0 := eq242630 X0
       grind)
    | exact resolve eq242630 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242630
  have eq242799 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq242730 X0
       have i₂ := eq753 X0
       grind)
    | exact superpose eq753 eq242730
    | (have j0 := eq242730 X0
       grind)
    | exact resolve eq242730 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242730
  have eq243026 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq242799 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq242799
    | (have j0 := eq242799 (σ X0)
       grind)
    | exact resolve eq242799 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242799
  have eq272166 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq976 (σ X0) (σ X0)
       have i₂ := eq243026 X0
       grind)
    | exact superpose eq243026 eq976
    | (have j1 := eq243026 X0
       grind)
    | exact resolve eq976 eq243026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243026
  have eq281888 : ∀ X0 : G, (k (M.op x y) X0) = (σ (τ (k y X0))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq11 (k (M.op x y) X0)
       have i₂ := eq199459 X0
       grind)
    | exact superpose eq199459 eq11
    | exact resolve eq11 eq199459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199459
  have eq281899 : ∀ X0 : G, (k y X0) = (k (M.op x y) X0) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq281888 X0
       have i₂ := eq11 (k y X0)
       grind)
    | exact superpose eq11 eq281888
    | exact resolve eq281888 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281888
  have eq281953 : y = (M.op y (k y x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq150137 x y
       have i₂ := eq281899 x
       grind)
    | exact superpose eq281899 eq150137
    | (have j0 := eq150137 x y
       grind)
    | exact resolve eq150137 eq281899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150137
  have eq281959 : (M.op x (M.op y y)) = (k y (M.op x (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq876 y x
       have i₂ := eq281899 (M.op x (M.op y y))
       grind)
    | exact superpose eq281899 eq876
    | exact resolve eq876 eq281899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876 eq281899
  have eq281992 : y = (M.op y (k y x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq281953
  have eq282013 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq281992
       have i₂ := eq82908
       grind)
    | exact superpose eq82908 eq281992
    | exact resolve eq281992 eq82908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281992
  have eq282395 : y = (k y (M.op y (M.op x y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq155869 y y
       have i₂ := eq282013
       grind)
    | exact superpose eq282013 eq155869
    | exact resolve eq155869 eq282013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155869 eq282013
  have eq282515 : y = (k y (M.op y (M.op x y))) := by
    first
    | (have j1 := eq1085 y x
       grind)
    | (have r₁ := eq282395
       have r₂ := eq1085 y x
       grind)
    | exact resolve eq282395 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085 eq282395
  have eq282668 : y = (k y (M.op x (M.op y y))) := by
    first
    | (have i₁ := eq282515
       have i₂ := eq1062 x y
       grind)
    | exact superpose eq1062 eq282515
    | exact resolve eq282515 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282515
  have eq282831 : y = (M.op x (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq281959
       have i₂ := eq282668
       grind)
    | exact superpose eq282668 eq281959
    | exact resolve eq281959 eq282668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281959 eq282668
  have eq284338 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq1533 x y X0
       have i₂ := eq282831
       grind)
    | exact superpose eq282831 eq1533
    | exact resolve eq1533 eq282831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533
  have eq284517 : ∀ X0 : G, (M.op y y) ≠ (M.op X0 (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq156249 X0 x (M.op y y)
       have i₂ := eq282831
       grind)
    | exact superpose eq282831 eq156249
    | exact resolve eq156249 eq282831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156249 eq282831
  have eq284534 : ∀ X0 : G, (M.op y y) ≠ (M.op X0 (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq284517 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284517
  have eq284645 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq284338 x
       have r₂ := eq284534 x
       grind)
    | exact resolve eq284338 eq284534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284338 eq284534
  have eq301887 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X0 (M.op X1 X0)) X1) ∨ (k (M.op X0 (M.op X1 X0)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29503 X0 X1 X1
       have i₂ := eq989 X0 X1
       grind)
    | exact superpose eq989 eq29503
    | (have j0 := eq29503 X0 X1 X1
       grind)
    | (have r₁ := eq29503 X0 X1 X1
       have r₂ := eq989 X0 X1
       grind)
    | exact resolve eq29503 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29503
  have eq301905 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X0 (M.op X1 X0)) X1) ∨ (k (M.op X0 (M.op X1 X0)) X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq301887 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301887
  have eq301908 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X0 (M.op X1 X0)) X1) ∨ (k (M.op X0 (M.op X1 X0)) X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq301905 X0 X1
       have j1 := eq992 X0 X1
       grind)
    | (have r₁ := eq301905 X0 X1
       have r₂ := eq992 X0 X1
       grind)
    | (have r₁ := eq301905 X1 X0
       have r₂ := eq992 X0 X1
       grind)
    | (have r₁ := eq301905 X0 X1
       have r₂ := eq992 (M.op X0 (M.op X1 X0)) (k (M.op X0 (M.op X1 X0)) X1)
       grind)
    | exact resolve eq301905 eq992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992 eq301905
  have eq331281 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (τ (M.op (σ X0) (σ X0))) ∨ (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq104393 (M.op X0 X0) X0
       have i₂ := eq109580 X0
       grind)
    | exact superpose eq109580 eq104393
    | (have j0 := eq104393 (M.op X0 X0) X0
       have j1 := eq109580 X0
       grind)
    | exact resolve eq104393 eq109580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104393 eq109580
  have eq331350 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (τ (M.op (σ X0) (σ X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq331281 X0
       have j1 := eq1158 X0 X0
       grind)
    | (have r₁ := eq331281 X0
       have r₂ := eq1158 X0 x
       grind)
    | exact resolve eq331281 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158 eq331281
  have eq331357 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq331350 X0
       have i₂ := eq753 X0
       grind)
    | exact superpose eq753 eq331350
    | (have j0 := eq331350 X0
       grind)
    | exact resolve eq331350 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331350
  have eq331361 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq331357 X0
       have i₂ := eq753 X0
       grind)
    | exact superpose eq753 eq331357
    | (have j0 := eq331357 X0
       grind)
    | exact resolve eq331357 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753 eq331357
  have eq331364 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq331361 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq331361
    | (have j0 := eq331361 (τ X0)
       grind)
    | exact resolve eq331361 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331361
  have eq349937 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (τ (M.op X0 X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq829 (τ X0) X1
       have i₂ := eq331364 X0
       grind)
    | exact superpose eq331364 eq829
    | (have j1 := eq331364 X0
       grind)
    | exact resolve eq829 eq331364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349961 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op X1 (M.op X1 (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq159718 (τ X0) X1
       have i₂ := eq331364 X0
       grind)
    | exact superpose eq331364 eq159718
    | (have j0 := eq159718 (τ X0) X1
       have j1 := eq331364 X0
       grind)
    | (have r₁ := eq159718 (τ X0) X1
       have r₂ := eq331364 X0
       grind)
    | exact resolve eq159718 eq331364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331364
  have eq350005 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op X1 (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq349961 X0 X1
       have j1 := eq159718 (τ X0) X1
       grind)
    | (have r₁ := eq349961 X0 X1
       have r₂ := eq159718 (τ X0) X1
       grind)
    | exact resolve eq349961 eq159718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349961
  have eq362032 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ (M.op X0 X0)) (τ X0))
       have i₂ := eq31144 X0
       grind)
    | exact superpose eq31144 eq10
    | (have j1 := eq31144 X0
       grind)
    | exact resolve eq10 eq31144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31144
  have eq374726 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (M.op (τ (M.op X0 X0)) (M.op X1 (M.op X1 (τ (M.op X0 X0))))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1981 X1 (τ (M.op X0 X0)) (τ X0)
       have i₂ := eq362032 X0
       grind)
    | exact superpose eq362032 eq1981
    | (have j1 := eq362032 X0
       grind)
    | exact resolve eq1981 eq362032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1981 eq362032
  have eq374736 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq374726 X0 x
       have i₂ := eq687 x (τ (M.op X0 X0))
       grind)
    | exact superpose eq687 eq374726
    | (have j0 := eq374726 X0 x
       grind)
    | exact resolve eq374726 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374726
  have eq374750 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq374736 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq374736
    | exact resolve eq374736 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374736
  have eq374977 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq374750 X0
       grind)
    | exact superpose eq374750 eq11
    | (have j1 := eq374750 X0
       grind)
    | exact resolve eq11 eq374750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374750
  have eq375407 : ∀ X0 X1 : G, (τ (σ X0)) ≠ X0 ∨ (τ (σ X0)) = (M.op X1 (M.op X1 (τ (σ X0)))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq350005 (σ X0) X1
       have i₂ := eq374977 X0
       grind)
    | exact superpose eq374977 eq350005
    | (have j0 := eq350005 (σ X0) X1
       have j1 := eq374977 X0
       grind)
    | exact resolve eq350005 eq374977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350005 eq374977
  have eq375439 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 (M.op X1 (τ (σ X0)))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq375407 X0 X1
       grind)
    | (have r₁ := eq375407 X0 X1
       have r₂ := eq10 X0
       grind)
    | exact resolve eq375407 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375407
  have eq375454 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq375439 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq375439
    | (have j0 := eq375439 X0 X1
       grind)
    | exact resolve eq375439 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375439
  have eq476313 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (τ (M.op (σ X0) (σ X0))))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq349937 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq349937
    | exact resolve eq349937 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349937
  have eq476494 : ∀ X0 X2 : G, (M.op (τ (M.op (σ X0) (σ X0))) (M.op X2 (M.op X2 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq1432 (τ (M.op (σ X0) (σ X0))) x x
       have i₂ := eq476313 X0 x
       grind)
    | exact superpose eq476313 eq1432
    | (have j1 := eq476313 X0 x
       grind)
    | exact resolve eq1432 eq476313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1432 eq476313
  have eq480666 : ∀ X0 X2 : G, (M.op (τ (M.op (σ X0) (σ X0))) X0) ≠ X0 ∨ (M.op X2 (M.op X2 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq157071 (τ (M.op (σ X0) (σ X0))) x X0 X2
       have i₂ := eq476494 X0 x
       grind)
    | exact superpose eq476494 eq157071
    | (have j0 := eq157071 X0 x X0 X2
       have j1 := eq476494 X0 X2
       grind)
    | exact resolve eq157071 eq476494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157071 eq476494
  have eq480740 : ∀ X0 X2 : G, (M.op (τ (M.op (σ X0) (σ X0))) X0) ≠ X0 ∨ (M.op X2 (M.op X2 X0)) = X0 := by
    intro X0 X2
    first
    | (have j0 := eq480666 X0 X2
       have j1 := eq159718 X0 X2
       grind)
    | (have r₁ := eq480666 X0 X2
       have r₂ := eq159718 X0 x
       grind)
    | exact resolve eq480666 eq159718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159718 eq480666
  have eq488524 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ X0 ∨ (k (M.op X0 (M.op X1 X0)) X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq301908 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301908
  have eq488624 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq488524 (M.op X1 X0) X1
       have i₂ := eq749 X0 X1 X1
       grind)
    | exact superpose eq749 eq488524
    | exact resolve eq488524 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488524
  have eq508781 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq158180 (M.op x X0) (M.op X1 X0)
       have i₂ := eq125894 X0 X1 x X1
       grind)
    | exact superpose eq125894 eq158180
    | (have j1 := eq125894 X0 X1 X1 x
       grind)
    | exact resolve eq158180 eq125894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125894 eq158180
  have eq508943 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq508781 X0 X1
       have j1 := eq488624 X0 X1
       grind)
    | (have r₁ := eq508781 X0 X1
       have r₂ := eq488624 X0 X1
       grind)
    | exact resolve eq508781 eq488624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488624 eq508781
  have eq508995 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq508943 X0 X1
       have i₂ := eq1080 X0 X1
       grind)
    | exact superpose eq1080 eq508943
    | (have j0 := eq508943 X0 X1
       grind)
    | exact resolve eq508943 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080 eq508943
  have eq509067 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ X1 ∨ (k X1 X2) = (M.op X2 X1) ∨ (k X1 X2) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq508995 X1 X2
       have i₂ := eq971 X2 X1 X0
       grind)
    | (have i₁ := eq508995 X1 X1
       have i₂ := eq971 X0 X1 X1
       grind)
    | exact superpose eq971 eq508995
    | (have j0 := eq508995 X1 X2
       have j1 := eq971 X2 X1 X2
       grind)
    | exact resolve eq508995 eq971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971
  have eq509120 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq508995 X0 X1
       have i₂ := eq1596 X1 X0 X0
       grind)
    | (have i₁ := eq508995 X1 x
       have i₂ := eq1596 X0 X1 x
       grind)
    | exact superpose eq1596 eq508995
    | (have j0 := eq508995 X0 X0
       have j1 := eq1596 X1 X0 x
       grind)
    | exact resolve eq508995 eq1596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596 eq508995
  have eq509173 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq509120 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509120
  have eq509182 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ X1 ∨ (k X1 X2) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq509067 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509067
  have eq509501 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq509173 X0 X1
       have i₂ := eq375454 X0 X0
       grind)
    | exact superpose eq375454 eq509173
    | (have j0 := eq509173 X0 X1
       have j1 := eq375454 X0 X1
       grind)
    | (have r₁ := eq509173 X0 X1
       have r₂ := eq375454 X0 X0
       grind)
    | exact resolve eq509173 eq375454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375454 eq509173
  have eq509579 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq509501 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509501
  have eq511621 : ∀ X0 X1 X2 : G, (M.op (τ (σ (M.op X0 X0))) X0) ≠ X0 ∨ (M.op X1 (M.op X1 X0)) = X0 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq480740 X0 X1
       have i₂ := eq509579 X0 X2
       grind)
    | exact superpose eq509579 eq480740
    | (have j0 := eq480740 X0 X1
       have j1 := eq509579 X0 X2
       grind)
    | exact resolve eq480740 eq509579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480740 eq509579
  have eq511719 : ∀ X0 X2 : G, (M.op (τ (σ (M.op X0 X0))) X0) ≠ X0 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X2
    first
    | (have j0 := eq511621 X0 x X2
       have j1 := eq509182 X0 X0 X2
       grind)
    | (have r₁ := eq511621 x X0 X2
       have r₂ := eq509182 X0 x X2
       grind)
    | exact resolve eq511621 eq509182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509182 eq511621
  have eq511756 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X0) ≠ X0 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq511719 X0 X2
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq511719
    | (have j0 := eq511719 X0 X2
       grind)
    | exact resolve eq511719 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511719
  have eq511766 : ∀ X0 X2 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq511756 X0 X2
       have i₂ := eq976 X0 X0
       grind)
    | exact superpose eq976 eq511756
    | (have j0 := eq511756 X0 X2
       grind)
    | exact resolve eq511756 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511756
  have eq518155 : ∀ X0 X1 X2 : G, (M.op X2 X0) ≠ (M.op X1 (M.op X1 (k (M.op X2 X0) X2))) ∨ (M.op X2 X0) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq150176 X2 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150176
  have eq518349 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (M.op X0 (M.op X0 (M.op X1 X2))) ∨ (M.op X1 X2) = (M.op X2 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq158195 X1 X2
       have i₂ := eq909 X2 X2 X0 X1
       grind)
    | (have i₁ := eq158195 X1 X1
       have i₂ := eq909 X0 X1 X1 X1
       grind)
    | exact superpose eq909 eq158195
    | (have j0 := eq158195 X1 X2
       grind)
    | exact resolve eq158195 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909 eq158195
  have eq543823 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (k X0 X1))) ≠ X0 ∨ (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq518155 (M.op X0 (M.op X1 X0)) X1 X1
       have i₂ := eq989 X0 X1
       grind)
    | exact superpose eq989 eq518155
    | exact resolve eq518155 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989 eq518155
  have eq543891 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (k X0 X1))) ≠ X0 ∨ (M.op X0 (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq543823 X0 X1 X2
       have i₂ := eq2328 X1 X0 X0
       grind)
    | (have i₁ := eq543823 X2 X0 X2
       have i₂ := eq2328 X0 X2 (M.op X2 (M.op X0 X2))
       grind)
    | exact superpose eq2328 eq543823
    | (have j0 := eq543823 X0 X1 X2
       grind)
    | exact resolve eq543823 eq2328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2328 eq543823
  have eq543902 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) ≠ X0 ∨ (M.op X0 (M.op X0 (M.op (σ (M.op X2 (M.op X2 (τ X0)))) X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq543891 X0 (σ (M.op X2 (M.op X2 (τ X0)))) X1
       have i₂ := eq156881 X0 X2
       grind)
    | exact superpose eq156881 eq543891
    | (have j0 := eq543891 X0 (σ (M.op X2 (M.op X2 (τ X0)))) X2
       grind)
    | exact resolve eq543891 eq156881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156881 eq543891
  have eq546200 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (σ (M.op X0 (M.op X0 (τ X1)))) ∨ (M.op X2 (M.op X2 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (M.op X2 (M.op X2 X1))
       have i₂ := eq82067 X1 X2 X0
       grind)
    | exact superpose eq82067 eq11
    | (have j1 := eq82067 X1 X2 X2
       grind)
    | exact resolve eq11 eq82067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82067
  have eq581397 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X1)) = (σ (M.op X0 (M.op X0 (τ X1)))) ∨ (M.op X3 (M.op X3 X1)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq679 X2 X1 X3
       have i₂ := eq546200 X0 X1 X3
       grind)
    | exact superpose eq546200 eq679
    | (have j1 := eq546200 X0 X1 X2
       grind)
    | exact resolve eq679 eq546200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq581402 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (σ (M.op X0 (M.op X0 (τ X1)))) X1) ∨ (M.op X2 (M.op X2 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1056 X2 X1
       have i₂ := eq546200 X0 X1 X2
       grind)
    | exact superpose eq546200 eq1056
    | (have j1 := eq546200 X0 X1 X2
       grind)
    | exact resolve eq1056 eq546200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056 eq546200
  have eq594958 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (M.op (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq272166 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq272166
    | exact resolve eq272166 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272166
  have eq603623 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op X1 (M.op X1 X0)) = (σ (M.op X2 (M.op X2 (τ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq829 X0 X0
       have i₂ := eq581397 X2 X0 X1 X0
       grind)
    | exact superpose eq581397 eq829
    | (have j1 := eq581397 X2 X0 X1 x
       grind)
    | exact resolve eq829 eq581397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581397
  have eq604002 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (τ X1))) = (τ (M.op X0 (M.op X0 X1))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X2 (M.op X2 (τ X1)))
       have i₂ := eq603623 X1 X0 X2
       grind)
    | exact superpose eq603623 eq10
    | (have j1 := eq603623 X1 X1 X2
       grind)
    | exact resolve eq10 eq603623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603623
  have eq605295 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ (M.op X0 (M.op X0 X1)))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq829 (τ X1) (τ X1)
       have i₂ := eq604002 X0 X1 (τ X1)
       grind)
    | exact superpose eq604002 eq829
    | (have j1 := eq604002 X0 X1 x
       grind)
    | exact resolve eq829 eq604002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604002
  have eq608028 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ (M.op X1 (M.op X1 (τ X0)))) (M.op X0 X0))) = X0 ∨ (M.op X2 (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq687 (σ (M.op X1 (M.op X1 (τ X0)))) X0
       have i₂ := eq581402 X1 X0 X2
       grind)
    | exact superpose eq581402 eq687
    | (have j1 := eq581402 X0 X0 X2
       grind)
    | exact resolve eq687 eq581402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581402
  have eq608148 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (σ (M.op X1 (M.op X1 (τ X0)))) X0))) = X0 ∨ (M.op X2 (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq608028 X0 X1 X2
       have i₂ := eq3500 X0 X0 (σ (M.op X1 (M.op X1 (τ X0))))
       grind)
    | exact superpose eq3500 eq608028
    | (have j0 := eq608028 X0 X1 X2
       grind)
    | exact resolve eq608028 eq3500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608028
  have eq608160 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (σ (M.op X1 (M.op X1 (τ X0)))) X0))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq608148 X0 X1 x
       have j1 := eq543902 X0 X1 X1
       grind)
    | (have r₁ := eq608148 X0 X1 X1
       have r₂ := eq543902 X0 X1 x
       grind)
    | exact resolve eq608148 eq543902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543902 eq608148
  have eq608323 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ (M.op X1 (M.op X1 (τ (M.op X0 X0))))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq905 X0 (M.op X0 X0) (σ (M.op X1 (M.op X1 (τ (M.op X0 X0)))))
       have i₂ := eq608160 (M.op X0 X0) X1
       grind)
    | exact superpose eq608160 eq905
    | exact resolve eq905 eq608160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608160
  have eq611265 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op X1 (M.op X1 (τ (M.op X0 X0))))) (M.op X2 (M.op X3 (M.op X3 (M.op X2 (M.op X0 X0)))))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17612 X2 X3 (σ (M.op X1 (M.op X1 (τ (M.op X0 X0))))) X0
       have i₂ := eq608323 X0 X1
       grind)
    | exact superpose eq608323 eq17612
    | exact resolve eq17612 eq608323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17612 eq608323
  have eq611562 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X1 (M.op X1 (τ (M.op X0 X0))))) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq611265 X0 X1 X2 x
       have i₂ := eq905 X0 x X2
       grind)
    | exact superpose eq905 eq611265
    | exact resolve eq611265 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611265
  have eq615127 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ (M.op X1 (M.op X1 (τ (M.op (M.op X0 X0) (M.op X0 X0)))))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq905 X0 (σ (M.op X1 (M.op X1 (τ (M.op (M.op X0 X0) (M.op X0 X0)))))) (σ (M.op X1 (M.op X1 (τ (M.op (M.op X0 X0) (M.op X0 X0))))))
       have i₂ := eq611562 (M.op X0 X0) X1 (σ (M.op X1 (M.op X1 (τ (M.op (M.op X0 X0) (M.op X0 X0))))))
       grind)
    | exact superpose eq611562 eq905
    | exact resolve eq905 eq611562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905 eq611562
  have eq615415 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ (M.op X1 (M.op X1 (τ (M.op X0 (M.op (M.op X0 X0) X0)))))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq615127 X0 X1
       have i₂ := eq1062 (M.op X0 X0) X0
       grind)
    | exact superpose eq1062 eq615127
    | exact resolve eq615127 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062 eq615127
  have eq615563 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ (M.op X1 (M.op X1 (τ (M.op X0 (M.op X0 X0)))))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq615415 X0 X1
       have i₂ := eq976 X0 X0
       grind)
    | exact superpose eq976 eq615415
    | exact resolve eq615415 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615415
  have eq615801 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq615563 X0 (τ X0)
       have i₂ := eq605295 X0 X0
       grind)
    | exact superpose eq605295 eq615563
    | (have j1 := eq605295 X0 X0
       grind)
    | exact resolve eq615563 eq605295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605295 eq615563
  have eq617033 : ∀ X0 : G, (M.op X0 (M.op (σ (M.op (τ X0) (τ X0))) (M.op X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq687 (σ (M.op (τ X0) (τ X0))) X0
       have i₂ := eq615801 X0
       grind)
    | exact superpose eq615801 eq687
    | (have j1 := eq615801 X0
       grind)
    | exact resolve eq687 eq615801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687 eq615801
  have eq617174 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op (σ (M.op (τ X0) (τ X0))) X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq617033 X0
       have i₂ := eq3500 X0 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | exact superpose eq3500 eq617033
    | (have j0 := eq617033 X0
       grind)
    | exact resolve eq617033 eq3500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3500 eq617033
  have eq620830 : ∀ X0 X1 : G, (M.op (σ (M.op (τ X0) (τ X0))) X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3336 (σ (M.op (τ X0) (τ X0))) X0 X0 X1
       have i₂ := eq617174 X0
       grind)
    | exact superpose eq617174 eq3336
    | (have j0 := eq3336 X0 X1 X0 X1
       have j1 := eq617174 X0
       grind)
    | (have r₁ := eq3336 X0 X1 x (M.op (M.op X0 (M.op X1 (M.op X1 (M.op X0 x)))) (M.op (M.op X0 (M.op X1 (M.op X1 (M.op X0 x)))) (M.op (σ (M.op (τ (M.op X0 (M.op X1 (M.op X1 (M.op X0 x))))) (τ (M.op X0 (M.op X1 (M.op X1 (M.op X0 x))))))) (M.op X0 (M.op X1 (M.op X1 (M.op X0 x)))))))
       have r₂ := eq617174 (M.op X0 (M.op X1 (M.op X1 (M.op X0 x))))
       grind)
    | (have r₁ := eq3336 X0 X1 x (M.op (M.op X0 (M.op X1 (M.op X1 (M.op X0 x)))) (M.op X0 (M.op X1 (M.op X1 (M.op X0 x)))))
       have r₂ := eq617174 (M.op X0 (M.op X1 (M.op X1 (M.op X0 x))))
       grind)
    | exact resolve eq3336 eq617174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3336 eq617174
  have eq620923 : ∀ X0 X1 : G, (M.op (σ (M.op (τ X0) (τ X0))) X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq620830 X0 X1
       have j1 := eq511766 X0 X1
       grind)
    | (have r₁ := eq620830 X0 (k X0 (σ (M.op (τ X0) (τ X0))))
       have r₂ := eq511766 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | (have r₁ := eq620830 X0 X1
       have r₂ := eq511766 X0 x
       grind)
    | exact resolve eq620830 eq511766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620830
  have eq621509 : ∀ X0 : G, (k X0 (M.op (σ (M.op (τ X0) (τ X0))) X0)) = (M.op (M.op (σ (M.op (τ X0) (τ X0))) X0) X0) := by
    intro X0
    first
    | (have j0 := eq620923 X0 (M.op (σ (M.op (τ X0) (τ X0))) X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq621510 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (σ (M.op (τ X0) (τ X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq621509 X0
       have i₂ := eq976 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | exact superpose eq976 eq621509
    | exact resolve eq621509 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976 eq621509
  have eq724658 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq620923 X0 X1
       have i₂ := eq594958 X0
       grind)
    | exact superpose eq594958 eq620923
    | (have j0 := eq620923 X0 X1
       have j1 := eq594958 X0
       grind)
    | (have r₁ := eq620923 X0 (σ (M.op (τ X0) (τ X0)))
       have r₂ := eq594958 X0
       grind)
    | (have r₁ := eq620923 X0 (M.op (M.op (σ (M.op (τ X0) (τ X0))) X0) (M.op (σ (M.op (τ X0) (τ X0))) X0))
       have r₂ := eq594958 (M.op (σ (M.op (τ X0) (τ X0))) X0)
       grind)
    | exact resolve eq620923 eq594958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594958 eq620923
  have eq724694 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq724658 X0 X1
       have j1 := eq511766 X0 X1
       grind)
    | (have r₁ := eq724658 X0 X1
       have r₂ := eq511766 X0 x
       grind)
    | exact resolve eq724658 eq511766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511766 eq724658
  have eq724761 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (M.op (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have j0 := eq724694 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724694
  have eq724762 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq724761 X0
       have i₂ := eq759 X0
       grind)
    | exact superpose eq759 eq724761
    | exact resolve eq724761 eq759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724761
  have eq724894 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq621510 X0
       have i₂ := eq724762 X0
       grind)
    | exact superpose eq724762 eq621510
    | exact resolve eq621510 eq724762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621510 eq724762
  have eq724940 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq724894 X0
       have i₂ := eq759 X0
       grind)
    | exact superpose eq759 eq724894
    | exact resolve eq724894 eq759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759 eq724894
  have eq725619 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq724940 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq724940
    | exact resolve eq724940 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq725807 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq724940 X0
       grind)
    | exact superpose eq724940 eq10
    | exact resolve eq10 eq724940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724940
  have eq726026 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (τ (M.op X1 X1)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6269 X0 X1
       have i₂ := eq725807 X1
       grind)
    | exact superpose eq725807 eq6269
    | (have j0 := eq6269 X0 X1
       grind)
    | exact resolve eq6269 eq725807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6269 eq725807
  have eq728048 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6262 X0 X1
       have i₂ := eq725619 X1
       grind)
    | exact superpose eq725619 eq6262
    | (have j0 := eq6262 X0 X1
       grind)
    | exact resolve eq6262 eq725619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6262
  have eq734319 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq829 (σ X0) X1
       have i₂ := eq725619 X0
       grind)
    | exact superpose eq725619 eq829
    | exact resolve eq829 eq725619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq739725 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq734319 y X0
       have i₂ := eq284645
       grind)
    | exact superpose eq284645 eq734319
    | exact resolve eq734319 eq284645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734319
  have eq741374 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq749 (σ (M.op x y)) x X0
       have i₂ := eq739725 x
       grind)
    | exact superpose eq739725 eq749
    | exact resolve eq749 eq739725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq741584 : ∀ X0 X1 : G, (σ y) ≠ (M.op X1 (M.op X1 (σ y))) ∨ (σ y) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq518349 X0 X0 (M.op X0 (σ (M.op x y)))
       have i₂ := eq739725 X0
       grind)
    | exact superpose eq739725 eq518349
    | exact resolve eq518349 eq739725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518349 eq739725
  have eq741822 : ∀ X1 : G, (σ y) ≠ (M.op X1 (M.op X1 (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X1
    first
    | (have i₁ := eq741584 x X1
       have i₂ := eq741374 x
       grind)
    | exact superpose eq741374 eq741584
    | (have j0 := eq741584 x X1
       grind)
    | exact resolve eq741584 eq741374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741374 eq741584
  have eq1518500 : ∀ X0 X1 : G, (τ (k X1 X0)) ≠ (τ (M.op X1 X1)) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq726026 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726026
  have eq1518636 : ∀ X0 X1 : G, (k (τ X0) X1) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ (σ X1)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1518500 (σ X1) X0
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq1518500
    | (have j0 := eq1518500 (σ X1) X0
       grind)
    | exact resolve eq1518500 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1518500
  have eq1518638 : ∀ X0 X1 : G, (k (τ X0) X1) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1518636 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1518636
    | (have j0 := eq1518636 X0 X1
       grind)
    | exact resolve eq1518636 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518636
  have eq1518642 : ∀ X0 X1 : G, (k X0 X1) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1518638 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1518638
    | exact resolve eq1518638 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518638
  have eq1518646 : ∀ X0 X1 : G, (k X0 X1) ≠ (τ (σ (M.op X0 X0))) ∨ (M.op X1 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1518642 X0 X1
       have i₂ := eq725619 X0
       grind)
    | exact superpose eq725619 eq1518642
    | (have j0 := eq1518642 X0 X1
       grind)
    | exact resolve eq1518642 eq725619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518642
  have eq1518647 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1518646 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1518646
    | (have j0 := eq1518646 X0 X1
       grind)
    | exact resolve eq1518646 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518646
  have eq1518648 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (σ (M.op X0 X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1518647 X0 X1
       have i₂ := eq725619 X0
       grind)
    | exact superpose eq725619 eq1518647
    | (have j0 := eq1518647 X0 X1
       grind)
    | exact resolve eq1518647 eq725619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518647
  have eq1518649 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1518648 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1518648
    | (have j0 := eq1518648 X0 X1
       grind)
    | exact resolve eq1518648 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518648
  have eq1518664 : ∀ X0 X1 : G, (k (σ X0) X1) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1518649 (σ X0) X1
       have i₂ := eq725619 X0
       grind)
    | exact superpose eq725619 eq1518649
    | exact resolve eq1518649 eq725619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725619 eq1518649
  have eq1518754 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1518664 X0 (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1518664
    | (have j0 := eq1518664 X0 (σ X1)
       grind)
    | exact resolve eq1518664 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518664
  have eq1518856 : (σ y) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1518754 y x
       have i₂ := eq82908
       grind)
    | exact superpose eq82908 eq1518754
    | (have j0 := eq1518754 y x
       grind)
    | exact resolve eq1518754 eq82908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518754
  have eq1518860 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1518856
       have i₂ := eq284645
       grind)
    | exact superpose eq284645 eq1518856
    | exact resolve eq1518856 eq284645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518856
  have eq1518861 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq1518860
       have i₂ := eq284645
       grind)
    | exact superpose eq284645 eq1518860
    | exact resolve eq1518860 eq284645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518860
  have eq1518862 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have r₁ := eq1518861
       have r₂ := eq16
       grind)
    | exact resolve eq1518861 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518861
  have eq1518914 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq728048 x y
       have i₂ := eq82908
       grind)
    | exact superpose eq82908 eq728048
    | (have j0 := eq728048 x y
       grind)
    | exact resolve eq728048 eq82908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82908 eq728048
  have eq1518917 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1518914
       have i₂ := eq284645
       grind)
    | exact superpose eq284645 eq1518914
    | exact resolve eq1518914 eq284645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284645 eq1518914
  have eq1518919 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1518917
       have r₂ := eq16
       grind)
    | exact resolve eq1518917 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518917
  have eq1519017 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq741822 (σ x)
       have i₂ := eq1518919
       grind)
    | exact superpose eq1518919 eq741822
    | exact resolve eq741822 eq1518919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741822
  have eq1521469 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1519017
       have r₂ := eq1518919
       grind)
    | exact resolve eq1519017 eq1518919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518919 eq1519017
  have eq1523475 : False := by grind
  exact eq1523475

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxx_y_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
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
  clear eq25
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq14 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  clear eq23 eq37
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
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
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
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
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq114
    | exact resolve eq114 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq485 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq14 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X2 X0 X1
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq935 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq627 X1 x X3
       have i₂ := eq627 X1 x X0
       grind)
    | exact superpose eq627 eq627
    | exact resolve eq627 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq948 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 x
       have i₂ := eq627 X1 x X0
       grind)
    | exact superpose eq627 eq14
    | exact resolve eq14 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq959 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X0 (M.op X2 X0) X2
       have i₂ := eq627 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq627 eq54
    | exact resolve eq54 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq966 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq959 X0 X1 X2
       have i₂ := eq54 X0 X0 X1
       grind)
    | exact superpose eq54 eq959
    | exact resolve eq959 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq959
  have eq989 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq948 X0 (M.op X0 X0)
       have i₂ := eq948 X0 X0
       grind)
    | exact superpose eq948 eq948
    | exact resolve eq948 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1098 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq989 X0
       grind)
    | exact superpose eq989 eq14
    | exact resolve eq14 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1629 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq935 X0 (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq948 X1 X0
       grind)
    | exact superpose eq948 eq935
    | exact resolve eq935 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935 eq948
  have eq1888 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq966 X0 X1 X0
       have i₂ := eq989 X0
       grind)
    | exact superpose eq989 eq966
    | exact resolve eq966 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966 eq989
  have eq3715 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq485 X0 X1 X1
       have i₂ := eq1888 X0 X1
       grind)
    | exact superpose eq1888 eq485
    | exact resolve eq485 eq1888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq3716 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3715 X0 x
       have i₂ := eq1888 (M.op X0 X0) x
       grind)
    | exact superpose eq1888 eq3715
    | exact resolve eq3715 eq1888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888 eq3715
  have eq3717 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  clear eq3716
  have eq24027 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24028 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq24027
    | exact resolve eq24027 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24027
  have eq24039 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq24028
       have r₂ := eq28
       grind)
    | exact resolve eq24028 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24028
  have eq24053 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X0 (M.op (σ y) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq24039 eq1629
    | exact resolve eq1629 eq24039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24039
  have eq24061 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24053 x
       have i₂ := eq1098 sF3 x
       grind)
    | exact superpose eq1098 eq24053
    | exact resolve eq24053 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24053
  have eq24062 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq24061
  have eq24078 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq24062 eq3717
    | exact resolve eq3717 eq24062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24062
  have eq24123 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq24078
    | exact resolve eq24078 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24078
  have eq24797 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq24123 eq115
    | exact resolve eq115 eq24123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq24123
  have eq24809 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq24797
  have eq24811 : y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq24809
       have r₂ := eq28
       grind)
    | exact resolve eq24809 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24809
  have eq24825 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op X0 (M.op y y))) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1629 x y X0
       have i₂ := eq24811
       grind)
    | exact superpose eq24811 eq1629
    | exact resolve eq1629 eq24811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24811
  have eq24833 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24825 x
       have i₂ := eq1098 y x
       grind)
    | exact superpose eq1098 eq24825
    | exact resolve eq24825 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24825
  have eq24834 : y = (M.op x x) := by grind
  clear eq24833
  have eq24850 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq3717 x
       have i₂ := eq24834
       grind)
    | exact superpose eq24834 eq3717
    | exact resolve eq3717 eq24834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24834
  have eq24895 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq24850
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24850
    | exact resolve eq24850 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq24850
  have eq25772 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq24895
       grind)
    | exact superpose eq24895 eq72
    | exact resolve eq72 eq24895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq24895
  have eq25798 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21 eq25772
    | exact resolve eq25772 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq25772
  have eq26402 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25798 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq25798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26403 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq26402
    | exact resolve eq26402 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26402
  have eq26414 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq26403
       have r₂ := eq28
       grind)
    | exact resolve eq26403 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26403
  have eq39244 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X0 (M.op (σ y) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq26414 eq1629
    | exact resolve eq1629 eq26414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1629 eq26414
  have eq39253 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq39244 x
       have i₂ := eq1098 sF3 x
       grind)
    | exact superpose eq1098 eq39244
    | exact resolve eq39244 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098 eq39244
  have eq39254 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq39253
  have eq39640 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq39254 eq3717
    | exact resolve eq3717 eq39254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3717 eq39254
  have eq39688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25798 eq39640
    | exact resolve eq39640 eq25798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25798 eq39640
  have eq39702 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq39688
    | exact resolve eq39688 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq39688
  have eq39705 : False := by grind
  exact eq39705
