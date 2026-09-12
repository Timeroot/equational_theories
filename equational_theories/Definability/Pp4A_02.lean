import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1434`: `x = (x ◇ x) ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation1434 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1434 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1434.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq498 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq499 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3233 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq499 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq499
    | exact resolve eq499 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq3279 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3233 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3233
    | (have j0 := eq3233 X0 X1
       grind)
    | exact resolve eq3233 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3233
  have eq3460 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (σ X1) = X0 ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq498 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq498 X0 X1
       grind)
    | exact superpose eq498 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq498 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq498 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq498 (σ X1) X1
       grind)
    | exact resolve eq13 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3462 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (k (τ (σ x)) y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq498 (σ x) y
       grind)
    | exact superpose eq498 eq16
    | (have j1 := eq498 (σ x) y
       grind)
    | (have r₁ := eq16
       have r₂ := eq498 (M.op (σ x) (σ y)) (M.op x y)
       grind)
    | exact resolve eq16 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq3467 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (σ X1) = X0 ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3460 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3460
  have eq3468 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3467 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3467
  have eq3472 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k (τ (σ x)) y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3462
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq3462
    | exact resolve eq3462 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3462
  have eq3487 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (τ (M.op (σ x) (σ y))) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3472
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3472
    | exact resolve eq3472 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3472
  have eq3714 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3468 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3468
    | exact resolve eq3468 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3468
  have eq3805 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3714 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq3714
    | (have j0 := eq3714 X0 X1
       grind)
    | exact resolve eq3714 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq3714
  have eq3928 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq3805 X1 X0
       grind)
    | exact superpose eq3805 eq11
    | (have j1 := eq3805 X1 X0
       grind)
    | exact resolve eq11 eq3805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3805
  have eq4048 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3928 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq3928
    | (have j0 := eq3928 X0 X1
       grind)
    | exact resolve eq3928 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3928
  have eq4068 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4048 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4048
    | (have j0 := eq4048 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq4048 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4088 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (k X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq4048 X0 (τ X1)
       grind)
    | exact superpose eq4048 eq19
    | (have j1 := eq4048 X0 (τ X1)
       grind)
    | exact resolve eq19 eq4048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq4048
  have eq4226 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4068 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq4068
    | (have j0 := eq4068 X0 X1
       grind)
    | exact resolve eq4068 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4068
  have eq4424 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4088 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4088
    | exact resolve eq4088 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4088
  have eq4479 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4424 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4424
    | (have j0 := eq4424 X0 X1
       grind)
    | exact resolve eq4424 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4424
  have eq12446 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4226 x y
       grind)
    | exact superpose eq4226 eq16
    | (have j1 := eq4226 x y
       grind)
    | exact resolve eq16 eq4226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4226
  have eq12525 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq12446
       have i₂ := eq3279 y x
       grind)
    | exact superpose eq3279 eq12446
    | (have j1 := eq3279 y x
       grind)
    | (have r₁ := eq12446
       have r₂ := eq3279 y x
       grind)
    | (have r₁ := eq12446
       have r₂ := eq3279 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq12446
       have r₂ := eq3279 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq12446 eq3279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12446
  have eq12526 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq12525
  have eq12651 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12526
       grind)
    | exact superpose eq12526 eq16
    | exact resolve eq16 eq12526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12526
  have eq12652 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq12651
       have r₂ := eq22 x
       grind)
    | exact resolve eq12651 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12651
  have eq12653 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (τ (M.op (σ x) (σ y))) = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3487
       have i₂ := eq12652
       grind)
    | exact superpose eq12652 eq3487
    | (have r₁ := eq3487
       have r₂ := eq12652
       grind)
    | exact resolve eq3487 eq12652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12652
  have eq12658 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (τ (M.op (σ x) (σ y))) = (k x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq12653
  have eq12659 : (τ (M.op (σ x) (σ y))) = (k x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq12658
  have eq12660 : (σ x) = (σ y) ∨ (τ (M.op (σ x) (σ y))) = (k x y) := by
    first
    | (have r₁ := eq12659
       have r₂ := eq3487
       grind)
    | exact resolve eq12659 eq3487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3487 eq12659
  have eq12662 : y = (τ (σ x)) ∨ (τ (M.op (σ x) (σ y))) = (k x y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq12660
       grind)
    | exact superpose eq12660 eq10
    | exact resolve eq10 eq12660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12660
  have eq12728 : x = y ∨ (τ (M.op (σ x) (σ y))) = (k x y) := by
    first
    | (have i₁ := eq12662
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12662
    | exact resolve eq12662 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12662
  have eq12730 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (τ (M.op (σ x) (σ y))) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12728
       grind)
    | exact superpose eq12728 eq16
    | exact resolve eq16 eq12728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12728
  have eq12731 : (τ (M.op (σ x) (σ y))) = (k x y) := by
    first
    | (have r₁ := eq12730
       have r₂ := eq22 x
       grind)
    | exact resolve eq12730 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12730
  have eq12744 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq12731
       grind)
    | exact superpose eq12731 eq11
    | exact resolve eq11 eq12731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12731
  have eq12900 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12744
       grind)
    | exact superpose eq12744 eq16
    | exact resolve eq16 eq12744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12744
  have eq12930 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq12900
       have i₂ := eq4479 y x
       grind)
    | exact superpose eq4479 eq12900
    | (have j1 := eq4479 y x
       grind)
    | (have r₁ := eq12900
       have r₂ := eq4479 y x
       grind)
    | (have r₁ := eq12900
       have r₂ := eq4479 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq12900
       have r₂ := eq4479 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq12900 eq4479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4479
  have eq12931 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq12900
       have i₂ := eq3279 y x
       grind)
    | exact superpose eq3279 eq12900
    | (have j1 := eq3279 y x
       grind)
    | (have r₁ := eq12900
       have r₂ := eq3279 y x
       grind)
    | (have r₁ := eq12900
       have r₂ := eq3279 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq12900
       have r₂ := eq3279 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq12900 eq3279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3279
  have eq12932 : (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq12931
  have eq12933 : x = y ∨ (M.op x x) = (k x y) := by grind
  clear eq12930
  have eq12947 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (M.op x x) = (k x y) := by
    first
    | (have i₁ := eq12900
       have i₂ := eq12933
       grind)
    | exact superpose eq12933 eq12900
    | exact resolve eq12900 eq12933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12933
  have eq12948 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (k x y) := by grind
  clear eq12947
  have eq12949 : (M.op x x) = (k x y) := by grind
  clear eq12948
  have eq12958 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12900
       have i₂ := eq12949
       grind)
    | exact superpose eq12949 eq12900
    | exact resolve eq12900 eq12949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12900 eq12949
  have eq12990 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq12958
       have i₂ := eq12932
       grind)
    | exact superpose eq12932 eq12958
    | exact resolve eq12958 eq12932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12932
  have eq12993 : x = y := by grind
  clear eq12990
  have eq13003 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12958
       have i₂ := eq12993
       grind)
    | exact superpose eq12993 eq12958
    | exact resolve eq12958 eq12993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12958 eq12993
  have eq13004 : False := by grind
  exact eq13004

/-- `Equation1434`: `x = (x ◇ x) ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation1434 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1434 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1434.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq86 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq87 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq91 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq87
  have eq92 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq91
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq86
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq86
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq86 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq99
    | exact resolve eq99 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq677 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq69
    | (have j0 := eq69 X0 X1
       grind)
    | exact resolve eq69 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq69
  have eq742 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq677 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq9687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq9687
    | exact resolve eq9687 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9687
  have eq9699 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq9688
       have r₂ := eq28
       grind)
    | exact resolve eq9688 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9688
  have eq9703 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq9699
    | exact resolve eq9699 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9699
  have eq9715 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (M.op (σ x) (σ y)) = (k (σ y) X0) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq9703 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq9703
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq9703
       grind)
    | exact resolve eq12 eq9703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9703
  have eq11850 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq9715
    | (have j0 := eq9715 (σ x)
       grind)
    | (have r₁ := eq9715 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq9715 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9715
  have eq11851 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq11850
  have eq11852 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq11851
  have eq11860 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq11852 eq101
    | exact resolve eq101 eq11852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq11852
  have eq11872 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq11860
  have eq11875 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq11872
       have r₂ := eq28
       grind)
    | exact resolve eq11872 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11872
  have eq11879 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq11875
       grind)
    | exact superpose eq11875 eq92
    | exact resolve eq92 eq11875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11889 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ (M.op x y) = (k y X0) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq12 y x
       have i₂ := eq11875
       grind)
    | exact superpose eq11875 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11875
       grind)
    | exact resolve eq12 eq11875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11875
  have eq11925 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq11879
    | exact resolve eq11879 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11879
  have eq18068 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11889 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11889
    | (have j0 := eq11889 x
       grind)
    | (have r₁ := eq11889 x
       have r₂ := eq19
       grind)
    | exact resolve eq11889 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11889
  have eq18069 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq18068
  have eq18070 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18069
  have eq18082 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq742 x y
       have i₂ := eq18070
       grind)
    | exact superpose eq18070 eq742
    | (have j0 := eq742 x y
       grind)
    | exact resolve eq742 eq18070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq18070
  have eq18086 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18082
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq18082
    | exact resolve eq18082 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18082
  have eq18097 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq18086
    | exact resolve eq18086 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18086
  have eq18103 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq18097
       have r₂ := eq11925
       grind)
    | exact resolve eq18097 eq11925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18097
  have eq18107 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18103
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq18103
    | exact resolve eq18103 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq18103
  have eq18111 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18107
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18107
    | exact resolve eq18107 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18107
  have eq18115 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18111
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18111
    | exact resolve eq18111 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18111
  have eq18119 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq18115
    | exact resolve eq18115 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18115
  have eq18123 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18119
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18119
    | exact resolve eq18119 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18119
  have eq18127 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18123
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18123
    | exact resolve eq18123 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18123
  have eq18128 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18127
  have eq18200 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq18128 eq11925
    | exact resolve eq11925 eq18128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11925 eq18128
  have eq18264 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18200
  have eq18270 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq18264
       have r₂ := eq28
       grind)
    | exact resolve eq18264 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18264
  have eq18273 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq18270 eq30
    | exact resolve eq30 eq18270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq18270
  have eq18393 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq18273
    | exact resolve eq18273 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18273
  have eq18394 : x = y := by grind
  clear eq18393
  have eq18562 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq18394
       grind)
    | exact superpose eq18394 eq19
    | exact resolve eq19 eq18394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq18563 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq18394
       grind)
    | exact superpose eq18394 eq25
    | exact resolve eq25 eq18394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq18394
  have eq18668 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq18563
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18563
    | exact resolve eq18563 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq18563
  have eq18683 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18668 eq27
    | exact resolve eq27 eq18668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq18668
  have eq18917 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq18683 eq68
    | exact resolve eq68 eq18683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq18683
  have eq18955 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18917
       have i₂ := eq18562
       grind)
    | exact superpose eq18562 eq18917
    | exact resolve eq18917 eq18562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18562 eq18917
  have eq18968 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18955 eq15
    | exact resolve eq15 eq18955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18955
  have eq19017 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq18968
    | exact resolve eq18968 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq18968
  have eq19027 : False := by grind
  exact eq19027

/-- `Equation1434`: `x = (x ◇ x) ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation1434 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1434 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1434.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq97 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq97 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq97 X0 X1
       grind)
    | exact superpose eq97 eq13
    | (have j0 := eq13 (k (σ X0) (σ X1)) (M.op (σ X0) (σ X1))
       have j1 := eq97 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq97 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq97 X0 X1
       grind)
    | exact resolve eq13 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq258 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq255 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq259 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq258 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq267 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq259 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq259
    | (have j0 := eq259 X0 X1
       grind)
    | exact resolve eq259 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq268 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq267 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq387 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq268 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq268
    | exact resolve eq268 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq268 x y
       grind)
    | exact superpose eq268 eq16
    | (have j1 := eq268 x y
       grind)
    | exact resolve eq16 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq413 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq387 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq387
    | (have j0 := eq387 X0 X1
       grind)
    | exact resolve eq387 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq387
  have eq439 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq413 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq413
    | exact resolve eq413 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq537 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq393
       have i₂ := eq439 x y
       grind)
    | exact superpose eq439 eq393
    | (have j1 := eq439 (σ x) (σ y)
       grind)
    | (have r₁ := eq393
       have r₂ := eq439 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq393
       have r₂ := eq439 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq393 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393 eq439
  have eq540 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq537
  have eq587 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq540
       grind)
    | exact superpose eq540 eq10
    | exact resolve eq10 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq622 : x = y ∨ x = y := by
    first
    | (have i₁ := eq587
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq587
    | exact resolve eq587 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq623 : x = y := by grind
  clear eq622
  have eq625 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq623
       grind)
    | exact superpose eq623 eq16
    | exact resolve eq16 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq626 : False := by grind
  exact eq626

/-- `Equation1434`: `x = (x ◇ x) ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation1434 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1434 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1434.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  clear eq49
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq72
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq72
    | exact resolve eq72 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq75
    | exact resolve eq75 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq76
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq76
    | exact resolve eq76 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq92 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq96 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq92
  have eq97 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq96
  have eq677 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 X1
       have i₂ := eq45 X1
       grind)
    | exact superpose eq45 eq69
    | (have j0 := eq69 X0 X1
       grind)
    | exact resolve eq69 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq69
  have eq742 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq677 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq9434 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq77 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9435 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq9434
    | exact resolve eq9434 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9434
  have eq9446 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq9435
       have r₂ := eq28
       grind)
    | exact resolve eq9435 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9435
  have eq9450 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq9446
    | exact resolve eq9446 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9446
  have eq9462 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (M.op (σ x) (σ y)) = (k X0 (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq9450 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq9450
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq9450
       grind)
    | exact resolve eq12 eq9450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9450
  have eq11550 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq9462
    | (have j0 := eq9462 (σ x)
       grind)
    | (have r₁ := eq9462 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq9462 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9462
  have eq11551 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq11550
  have eq11552 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq11551
  have eq11560 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq11552 eq77
    | exact resolve eq77 eq11552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq11552
  have eq11572 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq11560
  have eq11575 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq11572
       have r₂ := eq28
       grind)
    | exact resolve eq11572 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11572
  have eq11616 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq11575
       grind)
    | exact superpose eq11575 eq97
    | exact resolve eq97 eq11575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11626 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ (M.op x y) = (k X0 y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq11575
       grind)
    | exact superpose eq11575 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq11575
       grind)
    | exact resolve eq12 eq11575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11575
  have eq11662 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq11616
    | exact resolve eq11616 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11616
  have eq18078 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11626 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11626
    | (have j0 := eq11626 x
       grind)
    | (have r₁ := eq11626 x
       have r₂ := eq19
       grind)
    | exact resolve eq11626 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11626
  have eq18079 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq18078
  have eq18080 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18079
  have eq18093 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq742 x y
       have i₂ := eq18080
       grind)
    | exact superpose eq18080 eq742
    | (have j0 := eq742 x y
       grind)
    | exact resolve eq742 eq18080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq18080
  have eq18097 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18093
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq18093
    | exact resolve eq18093 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18093
  have eq18108 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq18097
    | exact resolve eq18097 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18097
  have eq18114 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq18108
       have r₂ := eq11662
       grind)
    | exact resolve eq18108 eq11662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18108
  have eq18118 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18114
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq18114
    | exact resolve eq18114 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq18114
  have eq18122 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18118
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18118
    | exact resolve eq18118 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18118
  have eq18126 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18122
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18122
    | exact resolve eq18122 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18122
  have eq18130 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq18126
    | exact resolve eq18126 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18126
  have eq18134 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18130
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18130
    | exact resolve eq18130 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18130
  have eq18138 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18134
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18134
    | exact resolve eq18134 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18134
  have eq18139 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18138
  have eq18210 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq18139 eq11662
    | exact resolve eq11662 eq18139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11662 eq18139
  have eq18274 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18210
  have eq18280 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq18274
       have r₂ := eq28
       grind)
    | exact resolve eq18274 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18274
  have eq18284 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq18280 eq30
    | exact resolve eq30 eq18280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq18280
  have eq18404 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq18284
    | exact resolve eq18284 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18284
  have eq18405 : x = y := by grind
  clear eq18404
  have eq18424 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq18405
       grind)
    | exact superpose eq18405 eq19
    | exact resolve eq19 eq18405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq18425 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq18405
       grind)
    | exact superpose eq18405 eq25
    | exact resolve eq25 eq18405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq18405
  have eq18530 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq18425
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18425
    | exact resolve eq18425 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq18425
  have eq18545 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18530 eq27
    | exact resolve eq27 eq18530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq18530
  have eq18778 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq18545 eq68
    | exact resolve eq68 eq18545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq18545
  have eq18816 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18778
       have i₂ := eq18424
       grind)
    | exact superpose eq18424 eq18778
    | exact resolve eq18778 eq18424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18424 eq18778
  have eq18829 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18816 eq15
    | exact resolve eq15 eq18816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18816
  have eq18876 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq18829
    | exact resolve eq18829 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq18829
  have eq18885 : False := by grind
  exact eq18885

/-- `Equation1437`: `x = (x ◇ x) ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation1437 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1437 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1437.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq84 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq189 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq84 X1 X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq193 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq189 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq194 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq193 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq196 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq194 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq194
    | (have j0 := eq194 X0 X1
       grind)
    | exact resolve eq194 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq200 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq196 X0 X1
       have j1 := eq192 X0 X1
       grind)
    | (have r₁ := eq196 X0 X1
       have r₂ := eq192 X0 X1
       grind)
    | (have r₁ := eq196 X0 (k X1 X0)
       have r₂ := eq192 X0 X1
       grind)
    | (have r₁ := eq196 X0 X0
       have r₂ := eq192 X0 X0
       grind)
    | exact resolve eq196 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq196
  have eq532 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq200 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq200
    | exact resolve eq200 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq200 x y
       grind)
    | exact superpose eq200 eq16
    | (have j1 := eq200 x y
       grind)
    | exact resolve eq16 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq563 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq532 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq532
    | (have j0 := eq532 X0 X1
       grind)
    | exact resolve eq532 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq532
  have eq568 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq563 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq563
    | exact resolve eq563 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq658 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq568 (τ X1) X0
       grind)
    | exact superpose eq568 eq18
    | (have j1 := eq568 (τ X1) X0
       grind)
    | exact resolve eq18 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq568
  have eq846 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq658 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq658
    | exact resolve eq658 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq894 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq846 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq846
    | (have j0 := eq846 X0 X1
       grind)
    | exact resolve eq846 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq1009 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq546
       have i₂ := eq894 y x
       grind)
    | exact superpose eq894 eq546
    | (have j1 := eq894 (σ y) (σ x)
       grind)
    | (have r₁ := eq546
       have r₂ := eq894 y x
       grind)
    | exact resolve eq546 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1010 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1009
  have eq1018 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1010
  have eq1028 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq546
       have i₂ := eq1018
       grind)
    | exact superpose eq1018 eq546
    | exact resolve eq546 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq1018
  have eq1029 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1028
  have eq1030 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1029
  have eq1083 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1030
  have eq1094 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1083
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1083
    | exact resolve eq1083 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1170 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1094
       grind)
    | exact superpose eq1094 eq16
    | exact resolve eq16 eq1094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094
  have eq1185 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1170
       have i₂ := eq894 y x
       grind)
    | exact superpose eq894 eq1170
    | (have j1 := eq894 y x
       grind)
    | (have r₁ := eq1170
       have r₂ := eq894 y x
       grind)
    | exact resolve eq1170 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq1186 : y = (M.op x x) := by grind
  clear eq1185
  have eq1244 : (M.op x y) = (k y x) := by grind
  clear eq1186
  have eq1257 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1170
       have i₂ := eq1244
       grind)
    | exact superpose eq1244 eq1170
    | exact resolve eq1170 eq1244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170 eq1244
  have eq1260 : False := by grind
  exact eq1260

/-- `Equation1437`: `x = (x ◇ x) ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_pxx_pxy_Equation1437 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1437 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1437.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X0))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 (M.op X2 X0)) X3 (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X0 X0) x
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq279 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq282 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq280 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq280 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq280 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq293 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq282 (σ X0)
       grind)
    | exact superpose eq282 eq15
    | exact resolve eq15 eq282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq282 (τ X0)
       grind)
    | exact superpose eq282 eq31
    | exact resolve eq31 eq282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq299 X0
       have i₂ := eq282 X0
       grind)
    | exact superpose eq282 eq299
    | exact resolve eq299 eq282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq312 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq293 X0
       have i₂ := eq282 X0
       grind)
    | exact superpose eq282 eq293
    | exact resolve eq293 eq282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq355 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq312 X0
       grind)
    | exact superpose eq312 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq312 X0
       grind)
    | exact superpose eq312 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X2 (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq312 X0
       grind)
    | exact superpose eq312 eq9
    | exact resolve eq9 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq62 (σ X0) (σ X0)
       have i₂ := eq312 X0
       grind)
    | exact superpose eq312 eq62
    | exact resolve eq62 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq312 X0
       grind)
    | exact superpose eq312 eq9
    | exact resolve eq9 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq359 X0
       have i₂ := eq312 (M.op X0 X0)
       grind)
    | exact superpose eq312 eq359
    | exact resolve eq359 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq362 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq355 X0 X1
       have j1 := eq356 X0 X1
       grind)
    | (have r₁ := eq355 X0 X1
       have r₂ := eq356 X0 X1
       grind)
    | exact resolve eq355 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq356
  have eq375 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op X1 (M.op X2 (τ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X0) X1 X2
       have i₂ := eq306 X0
       grind)
    | exact superpose eq306 eq9
    | exact resolve eq9 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1 (τ X0)
       have i₂ := eq306 X0
       grind)
    | exact superpose eq306 eq9
    | exact resolve eq9 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq360 X0 (σ (M.op X0 X0))
       have i₂ := eq312 (M.op X0 X0)
       grind)
    | exact superpose eq312 eq360
    | exact resolve eq360 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq378 X0 (τ (M.op X0 X0))
       have i₂ := eq306 (M.op X0 X0)
       grind)
    | exact superpose eq306 eq378
    | exact resolve eq378 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq471 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq362 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq362
    | exact resolve eq362 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ (M.op X1 X1)) (M.op X2 X0)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq357 X1 X2 X0
       have i₂ := eq362 X1 X0
       grind)
    | exact superpose eq362 eq357
    | (have j1 := eq362 X1 X0
       grind)
    | exact resolve eq357 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq484 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq362 X1 X0
       grind)
    | exact superpose eq362 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq362 X1 (σ X1)
       grind)
    | (have r₁ := eq13 X1 (σ X0)
       have r₂ := eq362 X0 X1
       grind)
    | exact resolve eq13 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq490 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq484 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq495 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq490 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq490 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq490 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq508 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq471 (τ X1) X0
       grind)
    | exact superpose eq471 eq18
    | (have j1 := eq471 (τ X1) X0
       grind)
    | exact resolve eq18 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq511 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq471 (σ X1) (σ X0)
       grind)
    | exact superpose eq471 eq15
    | (have j1 := eq471 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq471 X1 (τ X0)
       grind)
    | exact superpose eq471 eq17
    | (have j1 := eq471 X1 (τ X0)
       grind)
    | exact resolve eq17 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq731 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq508 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq508
    | exact resolve eq508 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq786 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq731 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq731
    | (have j0 := eq731 X0 X1
       grind)
    | exact resolve eq731 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq1051 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq495 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq495
    | exact resolve eq495 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1055 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq495 (σ X0) X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq495
    | exact resolve eq495 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq1086 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1055 X0 X1
       have i₂ := eq312 X0
       grind)
    | exact superpose eq312 eq1055
    | (have j0 := eq1055 X0 X1
       grind)
    | exact resolve eq1055 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055
  have eq1128 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1051 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1152 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1128 (σ X0) X1
       have i₂ := eq312 X0
       grind)
    | exact superpose eq312 eq1128
    | exact resolve eq1128 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1157 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1128 (M.op X0 X0) (M.op X1 (M.op X2 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq1128
    | (have j0 := eq1128 (M.op X0 X0) (M.op X1 (M.op X2 X0))
       grind)
    | exact resolve eq1128 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1166 : ∀ X0 : G, (τ X0) ≠ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1128 (τ (M.op X0 X0)) (τ (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq458 X0
       grind)
    | exact superpose eq458 eq1128
    | (have j0 := eq1128 (τ (M.op X0 X0)) (τ (M.op (M.op X0 X0) (M.op X0 X0)))
       grind)
    | exact resolve eq1128 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458 eq1128
  have eq1172 : ∀ X0 : G, (τ X0) ≠ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ X0) = (k (τ (M.op X0 X0)) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq1166 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166
  have eq1181 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ X0 ∨ (k (M.op X0 X0) (M.op X1 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1157 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq1187 : ∀ X0 : G, (τ X0) ≠ (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (τ X0) = (k (τ (M.op X0 X0)) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1172 X0
       have i₂ := eq306 (M.op X0 X0)
       grind)
    | exact superpose eq306 eq1172
    | (have j0 := eq1172 X0
       grind)
    | exact resolve eq1172 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq1188 : ∀ X0 : G, (τ X0) ≠ (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (τ X0) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq1187 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1198 : ∀ X0 : G, (τ X0) ≠ (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (τ X0) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1188 X0
       have i₂ := eq31 X0 (M.op X0 X0)
       grind)
    | exact superpose eq31 eq1188
    | (have j0 := eq1188 X0
       grind)
    | exact resolve eq1188 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1299 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (M.op X0 X0) (σ (M.op X1 (M.op X2 (τ X0))))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq519 (M.op X0 X0) (M.op X1 (M.op X2 (τ X0)))
       have i₂ := eq375 X0 X1 X2
       grind)
    | exact superpose eq375 eq519
    | exact resolve eq519 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375 eq519
  have eq1346 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) (σ (M.op X1 (M.op X2 (τ X0))))) = X0 ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1299 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1299
    | (have j0 := eq1299 X0 X1 X2
       grind)
    | exact resolve eq1299 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299
  have eq1476 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq511 x y
       grind)
    | exact superpose eq511 eq16
    | (have j1 := eq511 x y
       grind)
    | exact resolve eq16 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1512 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq511 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1582 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1512 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq1512
    | (have j0 := eq1512 (τ X0) (τ X1)
       grind)
    | exact resolve eq1512 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1512
  have eq1590 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1582 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1582
    | (have j0 := eq1582 X0 X1
       grind)
    | exact resolve eq1582 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1582
  have eq1593 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1590 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1590
    | (have j0 := eq1590 X0 X1
       grind)
    | exact resolve eq1590 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1590
  have eq1594 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1593 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1593
    | (have j0 := eq1593 X0 X1
       grind)
    | exact resolve eq1593 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593
  have eq1595 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1594 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1594
    | (have j0 := eq1594 X0 X1
       grind)
    | exact resolve eq1594 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594
  have eq1605 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1595 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq1595
    | (have j0 := eq1595 (τ X0) (τ X1)
       grind)
    | exact resolve eq1595 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1595
  have eq1690 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq1476
       have i₂ := eq1051 y x
       grind)
    | exact superpose eq1051 eq1476
    | (have j1 := eq1051 y x
       grind)
    | exact resolve eq1476 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1693 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1476
       have i₂ := eq786 y x
       grind)
    | exact superpose eq786 eq1476
    | (have j1 := eq786 (σ y) (σ x)
       grind)
    | (have r₁ := eq1476
       have r₂ := eq786 y x
       grind)
    | exact resolve eq1476 eq786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1694 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1693
  have eq1697 : (k x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1690
  have eq1715 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1476
       have i₂ := eq1697
       grind)
    | exact superpose eq1697 eq1476
    | exact resolve eq1476 eq1697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476
  have eq1724 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1715
  have eq4248 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1086 x y
       grind)
    | exact superpose eq1086 eq16
    | (have j1 := eq1086 x y
       grind)
    | exact resolve eq16 eq1086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4293 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq4248
  have eq4396 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4293
       have i₂ := eq786 y x
       grind)
    | exact superpose eq786 eq4293
    | (have j1 := eq786 y x
       grind)
    | (have r₁ := eq4293
       have r₂ := eq786 y x
       grind)
    | exact resolve eq4293 eq786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786 eq4293
  have eq4397 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq4396
  have eq11499 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ (M.op X0 X0))) (M.op X1 X2)) ∨ (k X2 (σ (τ X0))) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq476 X2 (τ X0) X1
       have i₂ := eq306 X0
       grind)
    | exact superpose eq306 eq476
    | (have j0 := eq476 X2 (τ X0) X2
       grind)
    | exact resolve eq476 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq11598 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (M.op X1 X2)) ∨ (k X2 (σ (τ X0))) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11499 X0 X1 X2
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq11499
    | (have j0 := eq11499 X0 X1 X2
       grind)
    | exact resolve eq11499 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11499
  have eq11612 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X2)) = X0 ∨ (k X2 (σ (τ X0))) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11598 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11598
    | (have j0 := eq11598 X0 X1 X2
       grind)
    | exact resolve eq11598 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11598
  have eq11621 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X2)) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11612 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11612
    | (have j0 := eq11612 X0 X1 X2
       grind)
    | exact resolve eq11612 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11612
  have eq11646 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X1) = (k (M.op X2 (M.op X3 X0)) X1) ∨ (M.op (M.op X1 X1) X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11621 X1 (M.op X0 X0) (M.op X2 (M.op X3 X0))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq11621
    | (have j0 := eq11621 X1 X1 (M.op X2 (M.op X3 X0))
       grind)
    | exact resolve eq11621 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16132 : ∀ X0 X1 X2 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (k (τ (M.op X0 X0)) (M.op X1 (M.op X2 (τ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (M.op X0 X0) (M.op X1 (M.op X2 (τ X0)))
       have i₂ := eq1346 X0 X1 X2
       grind)
    | exact superpose eq1346 eq22
    | (have j1 := eq1346 X0 X1 X2
       grind)
    | exact resolve eq22 eq1346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346
  have eq17896 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) ∨ (τ (σ X0)) = (τ (k (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1198 (σ X0)
       have i₂ := eq312 X0
       grind)
    | exact superpose eq312 eq1198
    | exact resolve eq1198 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq17920 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (σ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (τ (σ X0)) = (τ (k (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq17896 X0
       have i₂ := eq312 (M.op X0 X0)
       grind)
    | exact superpose eq312 eq17896
    | (have j0 := eq17896 X0
       grind)
    | exact resolve eq17896 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17896
  have eq17932 : ∀ X0 : G, (τ (σ X0)) ≠ (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (τ (σ X0)) = (τ (k (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq17920 X0
       have i₂ := eq10 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq10 eq17920
    | (have j0 := eq17920 X0
       grind)
    | exact resolve eq17920 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17920
  have eq17941 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ X0 ∨ (τ (σ X0)) = (τ (k (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq17932 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17932
    | (have j0 := eq17932 X0
       grind)
    | exact resolve eq17932 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17932
  have eq17948 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ (M.op X0 X0))) X0) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq17941 X0
       have i₂ := eq22 (σ (M.op X0 X0)) X0
       grind)
    | exact superpose eq22 eq17941
    | (have j0 := eq17941 X0
       grind)
    | exact resolve eq17941 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17941
  have eq17952 : ∀ X0 : G, (τ (σ X0)) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq17948 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq17948
    | (have j0 := eq17948 X0
       grind)
    | exact resolve eq17948 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17948
  have eq17955 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17952 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17952
    | (have j0 := eq17952 X0
       grind)
    | exact resolve eq17952 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17952
  have eq35853 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op (M.op (M.op X3 X2) (M.op X3 X2)) (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X3 X2) X4 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq61 X2 X0 X1 X3
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49911 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (τ X0)) ∨ (τ X0) = (k (τ (M.op X0 X0)) (M.op X1 (M.op X2 (τ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq16132 X0 X1 X2
       grind)
    | exact superpose eq16132 eq11
    | (have j1 := eq16132 X0 X1 X2
       grind)
    | exact resolve eq11 eq16132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16132
  have eq50081 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ (M.op X0 X0)) (M.op X1 (M.op X2 (τ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49911 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49911
    | (have j0 := eq49911 X0 X1 X2
       grind)
    | exact resolve eq49911 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49911
  have eq50192 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (σ (M.op X0 X0))) (M.op X1 (M.op X2 (τ (σ X0))))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50081 (σ X0) X1 X2
       have i₂ := eq312 X0
       grind)
    | exact superpose eq312 eq50081
    | exact resolve eq50081 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50081
  have eq50486 : ∀ X0 X1 X2 : G, (k (τ (σ (M.op X0 X0))) (M.op X1 (M.op X2 X0))) = X0 ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50192 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq50192
    | (have j0 := eq50192 X0 X1 X2
       grind)
    | exact resolve eq50192 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50192
  have eq50533 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (M.op X0 X0) (M.op X1 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50486 X0 X1 X2
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq50486
    | (have j0 := eq50486 X0 X1 X2
       grind)
    | exact resolve eq50486 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50486
  have eq50892 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (σ X0) (M.op X1 (σ X0))) ∨ (k (M.op X0 X0) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq360 X0 X1
       have i₂ := eq50533 X0 X1 X2
       grind)
    | exact superpose eq50533 eq360
    | (have j1 := eq50533 X0 X2 X3
       grind)
    | exact resolve eq360 eq50533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60500 : ∀ X0 X1 X2 X3 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (k (σ X0) (M.op X1 (σ X0))) ∨ (k (M.op X0 X0) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1152 X0 (M.op X1 (σ X0))
       have i₂ := eq50892 X0 X1 X2 X3
       grind)
    | exact superpose eq50892 eq1152
    | (have j0 := eq1152 X0 (M.op X1 (σ X0))
       have j1 := eq50892 X0 X1 X2 X3
       grind)
    | exact resolve eq1152 eq50892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152 eq50892
  have eq60554 : ∀ X0 X1 X2 X3 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (M.op X1 (σ X0))) ∨ (k (M.op X0 X0) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq60500 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60500
  have eq60575 : ∀ X0 X1 X2 X3 : G, (σ X0) = (k (σ X0) (M.op X1 (σ X0))) ∨ (k (M.op X0 X0) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq60554 X0 X1 X2 X3
       have j1 := eq50533 X0 X2 X3
       grind)
    | (have r₁ := eq60554 X0 X1 X2 X3
       have r₂ := eq50533 X0 X1 X2
       grind)
    | exact resolve eq60554 eq50533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50533 eq60554
  have eq64762 : ∀ X0 X1 X2 X3 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (M.op X1 (σ X0)))) ∨ (k (M.op X0 X0) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1605 (σ X0) (M.op X1 (σ X0))
       have i₂ := eq60575 X0 X1 X2 X3
       grind)
    | exact superpose eq60575 eq1605
    | (have j0 := eq1605 (σ X0) (M.op X1 (σ X0))
       have j1 := eq60575 X0 X1 X2 X3
       grind)
    | exact resolve eq1605 eq60575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1605 eq60575
  have eq64826 : ∀ X0 X1 X2 X3 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (M.op X1 (σ X0)))) ∨ (k (M.op X0 X0) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq64762 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64762
  have eq64870 : ∀ X0 X1 X2 X3 : G, (M.op X0 (τ (M.op X1 (σ X0)))) = X0 ∨ (k (M.op X0 X0) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64826 X0 X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq64826
    | (have j0 := eq64826 X0 X1 X2 X3
       grind)
    | exact resolve eq64826 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64826
  have eq65016 : ∀ X0 X1 X2 : G, (M.op X0 (τ (σ (M.op X0 X0)))) = X0 ∨ (k (M.op X0 X0) (M.op X1 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64870 X0 (σ (M.op (M.op X0 X0) (M.op X0 X0))) X1 X2
       have i₂ := eq361 X0
       grind)
    | exact superpose eq361 eq64870
    | (have j0 := eq64870 X0 X1 X1 X2
       grind)
    | exact resolve eq64870 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64870
  have eq65192 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (k (M.op X0 X0) (M.op X1 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65016 X0 X1 X2
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq65016
    | (have j0 := eq65016 X0 X1 X2
       grind)
    | exact resolve eq65016 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65016
  have eq65362 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (k (M.op X0 X0) (M.op X1 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (M.op X0 X0) X0
       have i₂ := eq65192 X0 X1 X2
       grind)
    | exact superpose eq65192 eq62
    | (have j1 := eq65192 X0 X1 X2
       grind)
    | exact resolve eq62 eq65192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq65192
  have eq65442 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) (M.op X1 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq65362 X0 X1 X2
       have j1 := eq1181 X0 X1 X2
       grind)
    | (have r₁ := eq65362 X0 X1 X2
       have r₂ := eq1181 X0 X1 X2
       grind)
    | exact resolve eq65362 eq1181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181 eq65362
  have eq65519 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ (M.op X0 X0)) (M.op X1 (M.op X2 (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65442 (σ X0) X1 X2
       have i₂ := eq312 X0
       grind)
    | exact superpose eq312 eq65442
    | exact resolve eq65442 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65626 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op y y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq65442 y X0 x
       have i₂ := eq1694
       grind)
    | exact superpose eq1694 eq65442
    | exact resolve eq65442 eq1694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65633 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op (M.op X1 X0) (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq65442 (M.op X1 X0) (M.op X0 X0) x
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq65442
    | exact resolve eq65442 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65644 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (k (M.op (M.op X2 (M.op X3 X1)) (M.op X2 (M.op X3 X1))) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq65442 (M.op X2 (M.op X3 X1)) (M.op (M.op X0 X1) (M.op X0 X1)) x
       have i₂ := eq35853 X2 X3 X1 X0 x
       grind)
    | exact superpose eq35853 eq65442
    | exact resolve eq65442 eq35853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65442
  have eq66055 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k (τ (M.op (M.op X0 (σ X1)) (M.op X0 (σ X1)))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op (M.op X0 (σ X1)) (M.op X0 (σ X1))) X1
       have i₂ := eq65633 (σ X1) X0
       grind)
    | exact superpose eq65633 eq22
    | exact resolve eq22 eq65633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq66383 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (M.op X0 X0) (τ (M.op X1 (M.op X2 (σ X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 (M.op X0 X0) (M.op X1 (M.op X2 (σ X0)))
       have i₂ := eq65519 X0 X1 X2
       grind)
    | exact superpose eq65519 eq28
    | exact resolve eq28 eq65519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq65519
  have eq66496 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) (τ (M.op X1 (M.op X2 (σ X0))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66383 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq66383
    | exact resolve eq66383 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66383
  have eq66718 : ∀ X0 X1 : G, (k (M.op X0 X0) (τ (M.op X1 (σ (M.op X0 X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq66496 X0 X1 (σ (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq361 X0
       grind)
    | exact superpose eq361 eq66496
    | exact resolve eq66496 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66720 : ∀ X0 X1 X2 : G, (k (M.op X1 X1) (τ (M.op X2 (σ (k X0 X1))))) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66496 X1 X2 (σ X0)
       have i₂ := eq1086 X0 X1
       grind)
    | exact superpose eq1086 eq66496
    | (have j1 := eq1086 X0 X1
       grind)
    | exact resolve eq66496 eq1086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086 eq66496
  have eq73162 : ∀ X0 X1 : G, (σ y) = (M.op (σ (M.op y y)) (M.op X0 (σ x))) ∨ y = (k (M.op y y) (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq357 y X0 (σ x)
       have i₂ := eq65626 X1
       grind)
    | exact superpose eq65626 eq357
    | (have j1 := eq65626 X1
       grind)
    | exact resolve eq357 eq65626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65626
  have eq79949 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (k (τ (M.op (σ (k X0 X1)) (σ (k X0 X1)))) X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq66055 (σ X0) X1
       have i₂ := eq511 X0 X1
       grind)
    | exact superpose eq511 eq66055
    | (have j1 := eq511 X0 X1
       grind)
    | exact resolve eq66055 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq80349 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (k (τ (σ (M.op (k X0 X1) (k X0 X1)))) X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79949 X0 X1
       have i₂ := eq312 (k X0 X1)
       grind)
    | exact superpose eq312 eq79949
    | (have j0 := eq79949 X0 X1
       grind)
    | exact resolve eq79949 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79949
  have eq80462 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (k (M.op (k X0 X1) (k X0 X1)) X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80349 X0 X1
       have i₂ := eq10 (M.op (k X0 X1) (k X0 X1))
       grind)
    | exact superpose eq10 eq80349
    | (have j0 := eq80349 X0 X1
       grind)
    | exact resolve eq80349 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80349
  have eq80511 : ∀ X0 X1 : G, (k X0 X1) = (k (M.op (k X0 X1) (k X0 X1)) X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80462 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq80462
    | (have j0 := eq80462 X0 X1
       grind)
    | exact resolve eq80462 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80462
  have eq144443 : ∀ X0 : G, (σ y) = (M.op (σ (M.op y y)) (σ (M.op x x))) ∨ y = (k (M.op y y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq73162 (σ (M.op (M.op x x) (M.op x x))) X0
       have i₂ := eq361 x
       grind)
    | exact superpose eq361 eq73162
    | (have j0 := eq73162 X0 X0
       grind)
    | exact resolve eq73162 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361 eq73162
  have eq154590 : (M.op x x) = (k (M.op (M.op x x) (M.op x x)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq80511 x y
       have i₂ := eq1697
       grind)
    | exact superpose eq1697 eq80511
    | (have j0 := eq80511 x y
       grind)
    | exact resolve eq80511 eq1697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1697 eq80511
  have eq154801 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (k (M.op (M.op x x) (M.op x x)) y) := by grind
  clear eq154590
  have eq158044 : ∀ X0 : G, (τ (σ y)) = (k (τ (M.op (σ y) (σ y))) (M.op x x)) ∨ y = (k (M.op y y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq66055 (σ (M.op y y)) (M.op x x)
       have i₂ := eq144443 X0
       grind)
    | exact superpose eq144443 eq66055
    | (have j1 := eq144443 X0
       grind)
    | exact resolve eq66055 eq144443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66055 eq144443
  have eq158163 : ∀ X0 : G, (τ (σ y)) = (k (τ (σ (M.op y y))) (M.op x x)) ∨ y = (k (M.op y y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq158044 X0
       have i₂ := eq312 y
       grind)
    | exact superpose eq312 eq158044
    | (have j0 := eq158044 X0
       grind)
    | exact resolve eq158044 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312 eq158044
  have eq158214 : ∀ X0 : G, (τ (σ y)) = (k (M.op y y) (M.op x x)) ∨ y = (k (M.op y y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq158163 X0
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq158163
    | (have j0 := eq158163 X0
       grind)
    | exact resolve eq158163 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158163
  have eq158241 : ∀ X0 : G, y = (k (M.op y y) (M.op x x)) ∨ y = (k (M.op y y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq158214 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq158214
    | (have j0 := eq158214 x
       grind)
    | exact resolve eq158214 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158214
  have eq158350 : y ≠ y ∨ y = (k (M.op y y) (M.op x x)) := by
    first
    | (have j0 := eq158241 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158241
  have eq158351 : y = (k (M.op y y) (M.op x x)) := by grind
  clear eq158350
  have eq158383 : y = (M.op (M.op y y) (M.op x x)) ∨ (M.op y y) = (M.op (M.op y y) (M.op x x)) := by
    first
    | (have i₁ := eq471 (M.op x x) (M.op y y)
       have i₂ := eq158351
       grind)
    | exact superpose eq158351 eq471
    | (have j0 := eq471 (M.op x x) (M.op y y)
       grind)
    | exact resolve eq471 eq158351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq158395 : y = (M.op (M.op y y) (M.op x x)) ∨ y = (M.op (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq1051 (M.op x x) (M.op y y)
       have i₂ := eq158351
       grind)
    | exact superpose eq158351 eq1051
    | exact resolve eq1051 eq158351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051 eq158351
  have eq158535 : ∀ X0 : G, y = (k (M.op y y) (M.op X0 x)) ∨ y = (M.op (M.op y y) (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq65644 X0 x (M.op y y) x
       have i₂ := eq158395
       grind)
    | exact superpose eq158395 eq65644
    | exact resolve eq65644 eq158395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65644 eq158395
  have eq160815 : ∀ X0 : G, (M.op y y) = (M.op (M.op y y) (M.op x x)) ∨ y = (M.op (M.op y y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq61 x (M.op y y) x x
       have i₂ := eq158383
       grind)
    | exact superpose eq158383 eq61
    | exact resolve eq61 eq158383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158383
  have eq161419 : ∀ X0 : G, x = (M.op (M.op x x) (M.op y y)) ∨ y = (M.op (M.op y y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq9 x (M.op y y) x
       have i₂ := eq160815 X0
       grind)
    | exact superpose eq160815 eq9
    | (have j1 := eq160815 X0
       grind)
    | exact resolve eq9 eq160815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160815
  have eq161511 : ∀ X0 : G, y = (M.op (M.op y y) x) ∨ y = (M.op (M.op y y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq9 y (M.op x x) y
       have i₂ := eq161419 X0
       grind)
    | exact superpose eq161419 eq9
    | (have j1 := eq161419 X0
       grind)
    | exact resolve eq9 eq161419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161419
  have eq161614 : ∀ X0 : G, y = (k (M.op y y) y) ∨ y = (M.op (M.op y y) (M.op y y)) ∨ y = (M.op (M.op y y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq158535 (M.op y y)
       have i₂ := eq161511 X0
       grind)
    | exact superpose eq161511 eq158535
    | (have j1 := eq161511 X0
       grind)
    | exact resolve eq158535 eq161511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161511
  have eq161684 : ∀ X0 : G, y = (M.op (M.op y y) (M.op X0 x)) ∨ y = (k (M.op y y) y) := by
    intro X0
    first
    | (have j0 := eq161614 X0
       have j1 := eq17955 y
       grind)
    | (have r₁ := eq161614 X0
       have r₂ := eq17955 y
       grind)
    | exact resolve eq161614 eq17955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161614
  have eq166299 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x x) = (k (M.op (M.op x x) (M.op x x)) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq154801
       grind)
    | exact superpose eq154801 eq16
    | exact resolve eq16 eq154801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154801
  have eq166377 : (σ x) ≠ (σ x) ∨ (M.op x x) = (k (M.op (M.op x x) (M.op x x)) y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq166299
       have i₂ := eq4397
       grind)
    | exact superpose eq4397 eq166299
    | exact resolve eq166299 eq4397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4397 eq166299
  have eq166388 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x x) = (k (M.op (M.op x x) (M.op x x)) y) := by grind
  clear eq166377
  have eq202153 : ∀ X0 X1 X2 : G, (τ X1) = (k (M.op (τ X1) (τ X1)) (τ (M.op X2 (σ (τ (k X0 X1)))))) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66720 (τ X1) (τ X0) X2
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq66720
    | exact resolve eq66720 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66720
  have eq202172 : ∀ X0 X1 X2 : G, (τ X1) = (k (M.op (τ X1) (τ X1)) (τ (M.op X2 (k X0 X1)))) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq202153 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq202153
    | (have j0 := eq202153 X0 X1 X2
       grind)
    | exact resolve eq202153 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202153
  have eq202177 : ∀ X0 X1 X2 : G, (τ X1) = (k (τ (M.op X1 X1)) (τ (M.op X2 (k X0 X1)))) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq202172 X0 X1 X2
       have i₂ := eq306 X1
       grind)
    | exact superpose eq306 eq202172
    | (have j0 := eq202172 X0 X1 X2
       grind)
    | exact resolve eq202172 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202172
  have eq202180 : ∀ X0 X1 X2 : G, (τ X1) = (τ (k (M.op X1 X1) (M.op X2 (k X0 X1)))) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq202177 X0 X1 X2
       have i₂ := eq31 (M.op X2 (k X0 X1)) (M.op X1 X1)
       grind)
    | exact superpose eq31 eq202177
    | (have j0 := eq202177 X0 X1 X2
       grind)
    | exact resolve eq202177 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq202177
  have eq202182 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (σ (τ (M.op X0 X0))) ∨ (τ X1) = (τ (k (M.op X1 X1) (M.op X2 (k X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq202180 X0 X1 X2
       have i₂ := eq306 X0
       grind)
    | exact superpose eq306 eq202180
    | (have j0 := eq202180 X0 X1 X2
       grind)
    | exact resolve eq202180 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq202180
  have eq202183 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (τ (k X0 X1))) ∨ (τ X1) = (τ (k (M.op X1 X1) (M.op X2 (k X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq202182 X0 X1 X2
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq202182
    | (have j0 := eq202182 X0 X1 X2
       grind)
    | exact resolve eq202182 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202182
  have eq202184 : ∀ X0 X1 X2 : G, (τ X1) = (τ (k (M.op X1 X1) (M.op X2 (k X0 X1)))) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq202183 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq202183
    | (have j0 := eq202183 X0 X1 X2
       grind)
    | exact resolve eq202183 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202183
  have eq202228 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (M.op X0 X0) (M.op X1 (k X2 X0))) ∨ (M.op X2 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k (M.op X0 X0) (M.op X1 (k X2 X0)))
       have i₂ := eq202184 X2 X0 X1
       grind)
    | exact superpose eq202184 eq11
    | (have j1 := eq202184 X2 X0 X2
       grind)
    | exact resolve eq11 eq202184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202184
  have eq202271 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) (M.op X1 (k X2 X0))) = X0 ∨ (M.op X2 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq202228 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq202228
    | (have j0 := eq202228 X0 X1 X2
       grind)
    | exact resolve eq202228 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202228
  have eq211658 : (M.op x y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (k (M.op (M.op x x) (M.op x x)) y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq166388
       grind)
    | exact superpose eq166388 eq10
    | exact resolve eq10 eq166388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166388
  have eq211668 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k (M.op (M.op x x) (M.op x x)) y) := by
    first
    | (have i₁ := eq211658
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq211658
    | exact resolve eq211658 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211658
  have eq211683 : (M.op x x) = (k (M.op (M.op x x) (M.op x x)) y) ∨ (M.op x x) = (k (M.op (M.op x x) (M.op x x)) y) := by
    first
    | (have i₁ := eq65633 y x
       have i₂ := eq211668
       grind)
    | exact superpose eq211668 eq65633
    | exact resolve eq65633 eq211668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211668
  have eq211684 : (M.op x x) = (k (M.op (M.op x x) (M.op x x)) y) := by grind
  clear eq211683
  have eq211698 : (M.op x x) = (M.op (M.op (M.op x x) (M.op x x)) y) ∨ y = (M.op (M.op y y) x) := by
    first
    | (have i₁ := eq11646 x y (M.op x x) x
       have i₂ := eq211684
       grind)
    | exact superpose eq211684 eq11646
    | (have j0 := eq11646 y (M.op x x) x x
       grind)
    | exact resolve eq11646 eq211684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11646 eq211684
  have eq211721 : ∀ X0 : G, y = (M.op (M.op y y) x) ∨ y = (M.op (M.op y y) (M.op X0 (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 (M.op (M.op x x) (M.op x x))
       have i₂ := eq211698
       grind)
    | exact superpose eq211698 eq9
    | exact resolve eq9 eq211698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211698
  have eq211841 : ∀ X0 : G, y = (k (M.op y y) y) ∨ y = (M.op (M.op y y) (M.op y y)) ∨ y = (M.op (M.op y y) (M.op X0 (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq158535 (M.op y y)
       have i₂ := eq211721 X0
       grind)
    | exact superpose eq211721 eq158535
    | (have j1 := eq211721 X0
       grind)
    | exact resolve eq158535 eq211721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158535 eq211721
  have eq211922 : ∀ X0 : G, y = (M.op (M.op y y) (M.op X0 (M.op x x))) ∨ y = (k (M.op y y) y) := by
    intro X0
    first
    | (have j0 := eq211841 X0
       have j1 := eq17955 y
       grind)
    | (have r₁ := eq211841 X0
       have r₂ := eq17955 y
       grind)
    | exact resolve eq211841 eq17955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17955 eq211841
  have eq212475 : y = (M.op (M.op y y) y) ∨ y = (k (M.op y y) y) ∨ y = (k (M.op y y) y) := by
    first
    | (have i₁ := eq211922 (M.op y y)
       have i₂ := eq161684 x
       grind)
    | exact superpose eq161684 eq211922
    | exact resolve eq211922 eq161684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161684 eq211922
  have eq212522 : y = (M.op (M.op y y) y) ∨ y = (k (M.op y y) y) := by grind
  clear eq212475
  have eq212617 : y = (k (M.op y y) y) ∨ y = (k (M.op y y) y) := by
    first
    | (have i₁ := eq65633 y (M.op y y)
       have i₂ := eq212522
       grind)
    | exact superpose eq212522 eq65633
    | exact resolve eq65633 eq212522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65633 eq212522
  have eq212655 : y = (k (M.op y y) y) := by grind
  clear eq212617
  have eq212875 : ∀ X0 : G, y = (k (M.op y y) (M.op X0 y)) ∨ y = (M.op (M.op y y) (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq202271 y x (M.op y y)
       have i₂ := eq212655
       grind)
    | exact superpose eq212655 eq202271
    | exact resolve eq202271 eq212655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202271 eq212655
  have eq215175 : y = (M.op (M.op y y) (M.op y y)) ∨ y = (M.op (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq282 (M.op y y)
       have i₂ := eq212875 y
       grind)
    | exact superpose eq212875 eq282
    | exact resolve eq282 eq212875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282 eq212875
  have eq215195 : y = (M.op (M.op y y) (M.op y y)) := by grind
  clear eq215175
  have eq215220 : (σ y) = (M.op (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq412 y
       have i₂ := eq215195
       grind)
    | exact superpose eq215195 eq412
    | exact resolve eq412 eq215195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq215255 : ∀ X0 X1 X2 : G, (M.op y y) = (M.op y (M.op X0 (M.op X1 (M.op X2 y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35853 X1 X2 y y X0
       have i₂ := eq215195
       grind)
    | exact superpose eq215195 eq35853
    | exact resolve eq35853 eq215195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215276 : y = (M.op (M.op y y) y) := by
    first
    | (have i₁ := eq9 y (M.op y y) y
       have i₂ := eq215195
       grind)
    | exact superpose eq215195 eq9
    | exact resolve eq9 eq215195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215618 : ∀ X0 : G, (M.op y y) = (k y (τ (M.op X0 (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq66718 (M.op y y) x
       have i₂ := eq215195
       grind)
    | exact superpose eq215195 eq66718
    | exact resolve eq66718 eq215195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66718
  have eq216090 : ∀ X0 : G, (M.op y y) = (M.op y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op y y) x (M.op y y)
       have i₂ := eq215195
       grind)
    | exact superpose eq215195 eq9
    | exact resolve eq9 eq215195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215195
  have eq218004 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq216090 x
       have i₂ := eq1694
       grind)
    | exact superpose eq1694 eq216090
    | exact resolve eq216090 eq1694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694
  have eq218553 : ∀ X0 : G, (σ y) = (M.op (σ (M.op y y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq357 y X0 (σ (M.op y y))
       have i₂ := eq215220
       grind)
    | exact superpose eq215220 eq357
    | exact resolve eq357 eq215220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq215220
  have eq223986 : ∀ X0 X1 : G, (M.op y y) = (M.op y (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq215255 X0 X1 (M.op y y)
       have i₂ := eq215276
       grind)
    | exact superpose eq215276 eq215255
    | exact resolve eq215255 eq215276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215255 eq215276
  have eq224173 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ (M.op y y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq223986 (M.op X0 X0) x
       have i₂ := eq11621 X0 x y
       grind)
    | exact superpose eq11621 eq223986
    | (have j1 := eq11621 X0 x y
       grind)
    | exact resolve eq223986 eq11621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11621 eq223986
  have eq229419 : ∀ X0 : G, (M.op y y) = (M.op y (τ (M.op X0 (σ y)))) ∨ (M.op y y) = (M.op y (τ (M.op X0 (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq215618 X0
       have i₂ := eq224173 (τ (M.op X0 (σ y)))
       grind)
    | exact superpose eq224173 eq215618
    | (have j1 := eq224173 (τ (M.op X0 (σ y)))
       grind)
    | exact resolve eq215618 eq224173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215618 eq224173
  have eq229522 : ∀ X0 : G, (M.op y y) = (M.op y (τ (M.op X0 (σ y)))) := by
    intro X0
    first
    | (have j0 := eq229419 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229419
  have eq233878 : (M.op y y) = (M.op y (τ (σ x))) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq229522 (σ x)
       have i₂ := eq218004
       grind)
    | exact superpose eq218004 eq229522
    | exact resolve eq229522 eq218004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218004 eq229522
  have eq233967 : (M.op y y) = (M.op y x) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq233878
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq233878
    | exact resolve eq233878 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233878
  have eq233968 : (M.op y y) = (M.op y x) := by grind
  clear eq233967
  have eq234273 : ∀ X0 : G, (σ y) = (M.op (σ (M.op y x)) (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq218553 X0
       have i₂ := eq233968
       grind)
    | exact superpose eq233968 eq218553
    | exact resolve eq218553 eq233968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218553
  have eq234320 : (M.op y x) = (M.op y (M.op y x)) := by
    first
    | (have i₁ := eq216090 y
       have i₂ := eq233968
       grind)
    | exact superpose eq233968 eq216090
    | exact resolve eq216090 eq233968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216090
  have eq235141 : ∀ X0 : G, y = (M.op (M.op y x) (M.op X0 (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq9 y x y
       have i₂ := eq233968
       grind)
    | exact superpose eq233968 eq9
    | exact resolve eq9 eq233968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233968
  have eq238298 : x = (M.op (M.op x x) (M.op y x)) := by
    first
    | (have i₁ := eq9 x y y
       have i₂ := eq234320
       grind)
    | exact superpose eq234320 eq9
    | exact resolve eq9 eq234320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234320
  have eq239995 : ∀ X0 : G, x = (M.op (M.op x x) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq61 x (M.op x x) y x
       have i₂ := eq238298
       grind)
    | exact superpose eq238298 eq61
    | exact resolve eq61 eq238298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq238298
  have eq241788 : ∀ X0 : G, (σ (M.op x x)) = (M.op (σ x) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq360 (M.op x x) x
       have i₂ := eq239995 x
       grind)
    | exact superpose eq239995 eq360
    | exact resolve eq360 eq239995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq246297 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op (M.op X0 x) (M.op X0 x)) y) := by
    intro X0
    first
    | (have i₁ := eq35853 x y x X0 (M.op y x)
       have i₂ := eq235141 x
       grind)
    | exact superpose eq235141 eq35853
    | exact resolve eq35853 eq235141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35853 eq235141
  have eq254902 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq246297 x
       have i₂ := eq239995 x
       grind)
    | exact superpose eq239995 eq246297
    | exact resolve eq246297 eq239995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239995 eq246297
  have eq255105 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1724
       have i₂ := eq254902
       grind)
    | exact superpose eq254902 eq1724
    | exact resolve eq1724 eq254902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724
  have eq255312 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq255105
  have eq255389 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq255312
       grind)
    | exact superpose eq255312 eq16
    | exact resolve eq16 eq255312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255422 : (σ y) = (M.op (σ (M.op y x)) (σ x)) := by
    first
    | (have i₁ := eq234273 (σ x)
       have i₂ := eq255312
       grind)
    | exact superpose eq255312 eq234273
    | exact resolve eq234273 eq255312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234273
  have eq255676 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq255389
       have i₂ := eq254902
       grind)
    | exact superpose eq254902 eq255389
    | exact resolve eq255389 eq254902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254902 eq255389
  have eq255809 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq241788 (σ (M.op y x))
       have i₂ := eq255422
       grind)
    | exact superpose eq255422 eq241788
    | exact resolve eq241788 eq255422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241788 eq255422
  have eq256039 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq255809
       have i₂ := eq255312
       grind)
    | exact superpose eq255312 eq255809
    | exact resolve eq255809 eq255312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255312 eq255809
  have eq256092 : False := by grind
  exact eq256092

/-- `Equation1443`: `x = (x ◇ y) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_Equation1443 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1443.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq40 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq82 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq31
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq31 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq158 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq81 x y
       grind)
    | exact superpose eq81 eq16
    | (have j1 := eq81 x y
       grind)
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq862 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq167 (τ X0) (τ X1)
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq167
    | (have j0 := eq167 (τ X0) (τ X1)
       grind)
    | exact resolve eq167 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq875 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq862 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq862
    | (have j0 := eq862 X0 X1
       grind)
    | exact resolve eq862 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq880 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq875 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq875
    | (have j0 := eq875 X0 X1
       grind)
    | exact resolve eq875 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875
  have eq884 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq880 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq880
    | (have j0 := eq880 X0 X1
       grind)
    | exact resolve eq880 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq887 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq884 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq884
    | (have j0 := eq884 X0 X1
       grind)
    | exact resolve eq884 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884
  have eq890 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq887 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq887
    | (have j0 := eq887 X0 X1
       grind)
    | exact resolve eq887 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq891 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq890 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq890
    | (have j0 := eq890 X0 X1
       grind)
    | exact resolve eq890 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq4602 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq82 X1 X0
       grind)
    | exact superpose eq82 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq82 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq82 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq82 X0 (σ X0)
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4618 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq82 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq4619 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4618 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4618
  have eq4620 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4602 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4602
  have eq4621 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4620 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4620
  have eq4623 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4619 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4619
    | (have j0 := eq4619 X0
       grind)
    | exact resolve eq4619 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4619
  have eq4666 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq4623 X0
       grind)
    | exact superpose eq4623 eq40
    | (have j1 := eq4623 X0
       grind)
    | exact resolve eq40 eq4623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq4623
  have eq4684 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4666 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4666
    | (have j0 := eq4666 X0
       grind)
    | exact resolve eq4666 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4666
  have eq4685 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4684 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4684
  have eq4687 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4685 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4685
    | exact resolve eq4685 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4715 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq4685 X0
       grind)
    | exact superpose eq4685 eq11
    | exact resolve eq11 eq4685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4778 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4687 X0
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq4687
    | exact resolve eq4687 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4687
  have eq4952 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4778 X0
       grind)
    | exact superpose eq4778 eq11
    | exact resolve eq11 eq4778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5065 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4952 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4952
    | exact resolve eq4952 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4952
  have eq5129 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0 X0
       have i₂ := eq5065 (τ X0)
       grind)
    | exact superpose eq5065 eq36
    | exact resolve eq36 eq5065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5186 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5129 X0
       have i₂ := eq4778 X0
       grind)
    | exact superpose eq4778 eq5129
    | exact resolve eq5129 eq4778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4778 eq5129
  have eq5775 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq5803 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5775 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq5775
    | exact resolve eq5775 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5775
  have eq5839 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5803 X0
       have i₂ := eq5065 X0
       grind)
    | exact superpose eq5065 eq5803
    | exact resolve eq5803 eq5065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5803
  have eq5858 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq5839
  have eq306359 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4621 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4621
    | exact resolve eq4621 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306580 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X1) X0
       have i₂ := eq4621 (σ X0) X1
       grind)
    | exact superpose eq4621 eq25
    | (have j1 := eq4621 (σ X0) X1
       grind)
    | exact resolve eq25 eq4621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4621
  have eq306868 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq306580 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq306580
    | (have j0 := eq306580 X0 X1
       grind)
    | exact resolve eq306580 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306580
  have eq306981 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq306359 X0 X1
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq306359
    | (have j0 := eq306359 X0 X1
       grind)
    | exact resolve eq306359 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306359
  have eq307083 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq306868 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq306868
    | (have j0 := eq306868 X0 X1
       grind)
    | exact resolve eq306868 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306868
  have eq307269 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq307083 X0 X1
       have i₂ := eq4715 X0
       grind)
    | exact superpose eq4715 eq307083
    | (have j0 := eq307083 X0 X1
       grind)
    | exact resolve eq307083 eq4715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307083
  have eq307367 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq307269 X0 X1
       have i₂ := eq5065 X0
       grind)
    | exact superpose eq5065 eq307269
    | (have j0 := eq307269 X0 X1
       grind)
    | exact resolve eq307269 eq5065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307269
  have eq307439 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq307367 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq307367
    | (have j0 := eq307367 X0 X1
       grind)
    | exact resolve eq307367 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307367
  have eq309055 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq306981 X0 X1
       grind)
    | exact superpose eq306981 eq11
    | (have j1 := eq306981 X0 X1
       grind)
    | exact resolve eq11 eq306981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306981
  have eq309433 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq309055 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq309055
    | (have j0 := eq309055 X0 X1
       grind)
    | exact resolve eq309055 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309055
  have eq309962 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq309433 (τ X0) X1
       grind)
    | exact superpose eq309433 eq18
    | (have j1 := eq309433 (τ X0) X1
       grind)
    | exact resolve eq18 eq309433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq309433
  have eq318935 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq307439 (τ X0) (τ X1)
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq307439
    | (have j0 := eq307439 (τ X1) (τ X0)
       grind)
    | exact resolve eq307439 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq307439
  have eq319715 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X1 X1))) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq318935 X0 X1
       have i₂ := eq5186 X1
       grind)
    | exact superpose eq5186 eq318935
    | (have j0 := eq318935 X0 X1
       grind)
    | exact resolve eq318935 eq5186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318935
  have eq320085 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq319715 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq319715
    | (have j0 := eq319715 X0 X1
       grind)
    | exact resolve eq319715 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319715
  have eq320320 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq320085 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq320085
    | (have j0 := eq320085 X0 X1
       grind)
    | exact resolve eq320085 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320085
  have eq320477 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq320320 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq320320
    | (have j0 := eq320320 X0 X1
       grind)
    | exact resolve eq320320 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320320
  have eq320583 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq320477 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq320477
    | (have j0 := eq320477 X0 X1
       grind)
    | exact resolve eq320477 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320477
  have eq321182 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq320583 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320583
  have eq342551 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (τ X1)
       have i₂ := eq309962 X1 (τ X0)
       grind)
    | exact superpose eq309962 eq19
    | (have j1 := eq309962 X1 (τ X0)
       grind)
    | exact resolve eq19 eq309962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq309962
  have eq342761 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq342551 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq342551
    | (have j0 := eq342551 X0 X1
       grind)
    | exact resolve eq342551 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342551
  have eq342974 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq342761 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq342761
    | (have j0 := eq342761 X0 X1
       grind)
    | exact resolve eq342761 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342761
  have eq343157 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (k X1 X0) = X0 ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq342974 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq342974
    | (have j0 := eq342974 X0 X1
       grind)
    | exact resolve eq342974 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342974
  have eq343328 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq343157 X0 X1
       have i₂ := eq5186 X0
       grind)
    | exact superpose eq5186 eq343157
    | (have j0 := eq343157 X0 X1
       grind)
    | exact resolve eq343157 eq5186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5186 eq343157
  have eq360903 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X0)) (τ (σ X1)))) ∨ (τ (σ X0)) = (τ (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq343328 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq343328
    | (have j0 := eq343328 (σ X1) (σ X0)
       grind)
    | exact resolve eq343328 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343328
  have eq361739 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op (τ (σ X0)) X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (τ (σ X0)) = (τ (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq360903 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq360903
    | (have j0 := eq360903 X0 X1
       grind)
    | exact resolve eq360903 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360903
  have eq362048 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (τ (σ X0)) = (τ (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq361739 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq361739
    | (have j0 := eq361739 X0 X1
       grind)
    | exact resolve eq361739 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361739
  have eq362251 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq362048 X0 X1
       have i₂ := eq4685 X1
       grind)
    | exact superpose eq4685 eq362048
    | (have j0 := eq362048 X0 X1
       grind)
    | exact resolve eq362048 eq4685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4685 eq362048
  have eq362405 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq362251 X0 X1
       have i₂ := eq5065 X1
       grind)
    | exact superpose eq5065 eq362251
    | (have j0 := eq362251 X0 X1
       grind)
    | exact resolve eq362251 eq5065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362251
  have eq362500 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq362405 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq362405
    | (have j0 := eq362405 X0 X1
       grind)
    | exact resolve eq362405 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362405
  have eq362883 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq158
       have i₂ := eq362500 x y
       grind)
    | exact superpose eq362500 eq158
    | (have j1 := eq362500 x y
       grind)
    | (have r₁ := eq158
       have r₂ := eq362500 x y
       grind)
    | exact resolve eq158 eq362500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq362500
  have eq363208 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq362883
  have eq363362 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq167 x y
       grind)
    | (have r₁ := eq363208
       have r₂ := eq167 x y
       grind)
    | exact resolve eq363208 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167 eq363208
  have eq363657 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq363362
       have i₂ := eq4715 y
       grind)
    | exact superpose eq4715 eq363362
    | exact resolve eq363362 eq4715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363362
  have eq363810 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq363657
       have i₂ := eq5065 y
       grind)
    | exact superpose eq5065 eq363657
    | exact resolve eq363657 eq5065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363657
  have eq369719 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq363810
       grind)
    | exact superpose eq363810 eq16
    | exact resolve eq16 eq363810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369903 : (τ (σ y)) ≠ (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq321182 (σ x) (σ y)
       have i₂ := eq363810
       grind)
    | exact superpose eq363810 eq321182
    | (have j0 := eq321182 (σ x) (σ y)
       grind)
    | exact resolve eq321182 eq363810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321182 eq363810
  have eq369909 : (σ x) = (M.op (σ y) (σ y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq369903
  have eq369915 : (σ x) = (σ (k y y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq369909
       have i₂ := eq4715 y
       grind)
    | exact superpose eq4715 eq369909
    | exact resolve eq369909 eq4715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4715 eq369909
  have eq369987 : (σ x) = (σ (M.op y y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq369915
       have i₂ := eq5065 y
       grind)
    | exact superpose eq5065 eq369915
    | exact resolve eq369915 eq5065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5065 eq369915
  have eq369988 : (σ x) = (σ (M.op y y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ x = (M.op y y) := by grind
  clear eq369987
  have eq370042 : (τ (σ y)) = (k (τ (σ x)) y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq369988
       have i₂ := eq25 (σ x) y
       grind)
    | exact superpose eq25 eq369988
    | exact resolve eq369988 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq369988
  have eq370077 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq370042
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq370042
    | exact resolve eq370042 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370042
  have eq370090 : y = (k x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq370077
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq370077
    | exact resolve eq370077 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370077
  have eq370111 : y ≠ y ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq891 x y
       have i₂ := eq370090
       grind)
    | exact superpose eq370090 eq891
    | (have j0 := eq891 x y
       grind)
    | (have r₁ := eq891 x y
       have r₂ := eq370090
       grind)
    | exact resolve eq891 eq370090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891 eq370090
  have eq370144 : y ≠ y ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq370111
  have eq370145 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq370144
  have eq374193 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq369719
       have i₂ := eq370145
       grind)
    | exact superpose eq370145 eq369719
    | exact resolve eq369719 eq370145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369719 eq370145
  have eq374194 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq374193
  have eq374195 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq374194
  have eq375397 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq5858 y
       have i₂ := eq374195
       grind)
    | exact superpose eq374195 eq5858
    | exact resolve eq5858 eq374195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374195
  have eq375678 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq375397
       have r₂ := eq16
       grind)
    | exact resolve eq375397 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375397
  have eq375789 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq375678
       grind)
    | exact superpose eq375678 eq10
    | exact resolve eq10 eq375678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375678
  have eq376275 : x = (M.op y y) := by
    first
    | (have i₁ := eq375789
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq375789
    | exact resolve eq375789 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375789
  have eq377378 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5858 y
       have i₂ := eq376275
       grind)
    | exact superpose eq376275 eq5858
    | exact resolve eq5858 eq376275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5858 eq376275
  have eq377662 : False := by grind
  exact eq377662

/-- `Equation1443`: `x = (x ◇ y) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxy_pxx_pxy_Equation1443 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1443.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) (M.op (M.op X0 X1) X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op X0 (M.op X0 x)) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X2 (M.op X0 (M.op X0 x))
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
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
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1 (M.op X0 (M.op X0 x))
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
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
  have eq115 : ∀ X0 X1 X2 : G, (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) (k X1 (σ X2))
       have i₂ := eq22 X1 X2 X0
       grind)
    | exact superpose eq22 eq14
    | (have j0 := eq14 (k X1 (σ X2)) (k X1 (σ X2))
       grind)
    | exact resolve eq14 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq208 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq73 X0 X0
       grind)
    | exact superpose eq73 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq73 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq73 X0 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq73 X0 X1
       grind)
    | exact resolve eq12 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq213 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq208 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq215 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq213 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq213 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq213 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq239 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq215 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq215
    | (have j0 := eq215 (τ X0) X1
       grind)
    | exact resolve eq215 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq241 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq239 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq239
    | (have j0 := eq239 X0 X1
       grind)
    | exact resolve eq239 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq244 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq241 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq241
    | (have j0 := eq241 X0 X1
       grind)
    | exact resolve eq241 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq250 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq244 (τ X0) X1
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq244
    | (have j0 := eq244 (τ X0) X1
       grind)
    | exact resolve eq244 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq2460 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq74 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq2461 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq2460 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2460
  have eq2465 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2461 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2461
    | (have j0 := eq2461 X0
       grind)
    | exact resolve eq2461 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2461
  have eq2471 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2465 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2465
    | exact resolve eq2465 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2465
  have eq2508 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2471 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq2471
    | (have j0 := eq2471 X0
       grind)
    | exact resolve eq2471 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2471
  have eq2513 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq2508 X0
       grind)
    | exact superpose eq2508 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq2508 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq2508 X0
       grind)
    | exact resolve eq12 eq2508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2508
  have eq2530 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2513 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2513
  have eq2628 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq2530 X0 X1
       grind)
    | exact superpose eq2530 eq11
    | (have j1 := eq2530 X0 X1
       grind)
    | exact resolve eq11 eq2530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2530
  have eq2705 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2628 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq2628
    | (have j0 := eq2628 X0 X0
       grind)
    | exact resolve eq2628 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2628
  have eq2811 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2705 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2705
  have eq2812 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2811 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2811
  have eq2928 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq250 X0 X1
       have i₂ := eq2812 X0
       grind)
    | exact superpose eq2812 eq250
    | (have j0 := eq250 X0 X1
       grind)
    | exact resolve eq250 eq2812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq2952 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2812 (σ X0)
       grind)
    | exact superpose eq2812 eq15
    | exact resolve eq15 eq2812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2958 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq2812 (τ X0)
       grind)
    | exact superpose eq2812 eq34
    | exact resolve eq34 eq2812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3003 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2958 X0
       have i₂ := eq2812 X0
       grind)
    | exact superpose eq2812 eq2958
    | exact resolve eq2958 eq2812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2958
  have eq3009 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2952 X0
       have i₂ := eq2812 X0
       grind)
    | exact superpose eq2812 eq2952
    | exact resolve eq2952 eq2812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2952
  have eq3230 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (M.op (τ (M.op X0 X0)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (τ X0) (τ X0) x
       have i₂ := eq3003 X0
       grind)
    | exact superpose eq3003 eq19
    | exact resolve eq19 eq3003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3231 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (M.op (τ (M.op X0 X0)) X1) (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (τ X0) (τ X0) x
       have i₂ := eq3003 X0
       grind)
    | exact superpose eq3003 eq20
    | exact resolve eq20 eq3003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3317 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq3009 X0
       grind)
    | exact superpose eq3009 eq9
    | exact resolve eq9 eq3009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3318 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq3009 X0
       grind)
    | exact superpose eq3009 eq9
    | exact resolve eq9 eq3009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3319 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ (M.op X0 X0)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X0) (σ X0) x
       have i₂ := eq3009 X0
       grind)
    | exact superpose eq3009 eq19
    | exact resolve eq19 eq3009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq4325 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq67 (σ (M.op X0 X0)) (M.op (σ X0) (M.op (σ X0) x))
       have i₂ := eq3317 X0 x
       grind)
    | exact superpose eq3317 eq67
    | exact resolve eq67 eq3317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3317
  have eq7203 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (τ (M.op X0 (M.op X0 X1))) (M.op (τ X0) (M.op (τ X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3230 (M.op X0 (M.op X0 X2)) X1
       have i₂ := eq9 X0 (M.op X0 X2) X2
       grind)
    | exact superpose eq9 eq3230
    | exact resolve eq3230 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7205 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (M.op (σ X0) (σ (M.op X0 X0)))) (M.op (τ (σ X0)) (M.op (τ (σ X0)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3230 (M.op (σ X0) (σ (M.op X0 X0))) X1
       have i₂ := eq3318 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq3318 eq3230
    | exact resolve eq3230 eq3318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3230 eq3318
  have eq7277 : ∀ X0 X1 : G, (M.op (τ (M.op (σ X0) (σ (M.op X0 X0)))) (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7205 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7205
    | exact resolve eq7205 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7205
  have eq8052 : ∀ X0 X1 X2 : G, (M.op (τ (M.op (σ X0) (M.op (σ X0) X1))) (M.op X0 (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7203 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7203
    | exact resolve eq7203 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7203
  have eq8370 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (τ (M.op (σ X0) (M.op (σ X0) X1))))) = X0 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20 (τ (M.op (σ X0) (M.op (σ X0) X1))) (M.op X0 (M.op X0 x)) x
       have i₂ := eq8052 X0 X1 x
       grind)
    | exact superpose eq8052 eq20
    | exact resolve eq20 eq8052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8052
  have eq10984 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op X0 (M.op X0 X1))) (M.op (σ X0) (M.op (σ X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3319 (M.op X0 (M.op X0 X2)) X1
       have i₂ := eq9 X0 (M.op X0 X2) X2
       grind)
    | exact superpose eq9 eq3319
    | exact resolve eq3319 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3319
  have eq12626 : ∀ X0 X1 X3 : G, (σ X0) = (M.op (M.op (σ X0) X3) (M.op (σ X0) (σ (M.op X0 (M.op X0 X1))))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20 (σ (M.op X0 (M.op X0 X1))) (M.op (σ X0) (M.op (σ X0) x)) x
       have i₂ := eq10984 X0 X1 x
       grind)
    | exact superpose eq10984 eq20
    | exact resolve eq20 eq10984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq10984
  have eq14628 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op (M.op (τ (σ X0)) X2) (M.op (τ (σ X0)) (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X1))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3231 (M.op (σ X0) (σ (M.op X0 (M.op X0 X1)))) X1
       have i₂ := eq12626 X0 X1 (σ (M.op X0 (M.op X0 X1)))
       grind)
    | exact superpose eq12626 eq3231
    | exact resolve eq3231 eq12626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3231 eq12626
  have eq14680 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (τ (M.op (σ X0) (σ (M.op X0 (M.op X0 X1))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14628 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14628
    | exact resolve eq14628 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14628
  have eq30988 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op (k X1 X0) (k X1 X0)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) ∨ (σ (k X2 (k (τ X1) (τ X0)))) = (M.op (σ X2) (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq115 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq115
    | (have j0 := eq115 X2 X1 X2
       grind)
    | exact resolve eq115 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq31241 : ∀ X0 X1 X2 : G, (σ X2) = (σ (M.op X2 X2)) ∨ (k X1 X0) = (M.op (k X1 X0) (k X1 X0)) ∨ (σ (k X2 (k (τ X1) (τ X0)))) = (M.op (σ X2) (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30988 X0 X1 X2
       have i₂ := eq3009 X2
       grind)
    | exact superpose eq3009 eq30988
    | (have j0 := eq30988 X0 X1 X2
       grind)
    | exact resolve eq30988 eq3009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30988
  have eq31333 : ∀ X0 X1 X2 : G, (M.op (σ X2) (k X1 X0)) = (σ (k X2 (τ (k X1 X0)))) ∨ (σ X2) = (σ (M.op X2 X2)) ∨ (k X1 X0) = (M.op (k X1 X0) (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31241 X0 X1 X2
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq31241
    | (have j0 := eq31241 X0 X1 X2
       grind)
    | exact resolve eq31241 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31241
  have eq31385 : ∀ X0 X1 X2 : G, (M.op (σ X2) (k X1 X0)) = (k (σ X2) (k X1 X0)) ∨ (σ X2) = (σ (M.op X2 X2)) ∨ (k X1 X0) = (M.op (k X1 X0) (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31333 X0 X1 X2
       have i₂ := eq18 (k X1 X0) X2
       grind)
    | exact superpose eq18 eq31333
    | (have j0 := eq31333 X0 X1 X2
       grind)
    | exact resolve eq31333 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31333
  have eq31402 : ∀ X0 X1 X2 : G, (M.op (σ X2) (k X1 X0)) = (k (σ X2) (k X1 X0)) ∨ (σ X2) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq31385 X0 X1 X2
       have j1 := eq12 (σ X2) (k X1 X0)
       grind)
    | (have r₁ := eq31385 X0 X1 X2
       have r₂ := eq12 X0 (k X1 X0)
       grind)
    | exact resolve eq31385 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31385
  have eq31411 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (M.op X0 (k X1 X2)) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31402 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31402
    | exact resolve eq31402 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31402
  have eq31548 : ∀ X0 X1 X2 : G, (σ (τ (M.op X0 X0))) = X0 ∨ (k X0 (k X1 X2)) = (M.op X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31411 X0 X1 X2
       have i₂ := eq3003 X0
       grind)
    | exact superpose eq3003 eq31411
    | (have j0 := eq31411 X0 X1 X2
       grind)
    | exact resolve eq31411 eq3003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31411
  have eq31558 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (M.op X0 (k X1 X2)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31548 X0 X1 X2
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq31548
    | (have j0 := eq31548 X0 X1 X2
       grind)
    | exact resolve eq31548 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31548
  have eq31564 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31558 X0 X0 X0
       have i₂ := eq2812 X0
       grind)
    | exact superpose eq2812 eq31558
    | (have j0 := eq31558 X1 X1 x
       grind)
    | exact resolve eq31558 eq2812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2812 eq31558
  have eq32181 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31564 (M.op X0 (τ (M.op (σ X0) (M.op (σ X0) X1)))) X1
       have i₂ := eq8370 X0 X1 (τ (M.op (σ X0) (M.op (σ X0) X1)))
       grind)
    | exact superpose eq8370 eq31564
    | (have j0 := eq31564 X0 X1
       grind)
    | exact resolve eq31564 eq8370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8370 eq31564
  have eq32406 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq32181 (τ X1) X0
       grind)
    | exact superpose eq32181 eq18
    | (have j1 := eq32181 X0 X0
       grind)
    | exact resolve eq18 eq32181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq32446 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq32181 (σ X1) (σ X0)
       grind)
    | exact superpose eq32181 eq15
    | (have j1 := eq32181 X0 (σ X0)
       grind)
    | exact resolve eq15 eq32181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32469 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 X0
       have i₂ := eq32181 (τ X1) (τ X0)
       grind)
    | exact superpose eq32181 eq34
    | (have j1 := eq32181 X0 (τ X0)
       grind)
    | exact resolve eq34 eq32181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq32181
  have eq32553 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32469 X0 X1
       have i₂ := eq3003 X0
       grind)
    | exact superpose eq3003 eq32469
    | (have j0 := eq32469 X0 X1
       grind)
    | exact resolve eq32469 eq3003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32469
  have eq32575 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32446 X0 X1
       have i₂ := eq3009 X0
       grind)
    | exact superpose eq3009 eq32446
    | (have j0 := eq32446 X0 X1
       grind)
    | exact resolve eq32446 eq3009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32446
  have eq34150 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32406 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32406
    | (have j0 := eq32406 X1 X1
       grind)
    | exact resolve eq32406 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34351 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34150 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq34150
    | (have j0 := eq34150 X0 X1
       grind)
    | exact resolve eq34150 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34150
  have eq35059 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq32553 X0 X1
       grind)
    | exact superpose eq32553 eq11
    | (have j1 := eq32553 X0 X1
       grind)
    | exact resolve eq11 eq32553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32553
  have eq35275 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35059 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35059
    | (have j0 := eq35059 X0 X1
       grind)
    | exact resolve eq35059 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35059
  have eq35326 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35275 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq35275
    | (have j0 := eq35275 X1 X1
       grind)
    | exact resolve eq35275 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35275
  have eq35634 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35326 X0 X1
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq35326
    | (have j0 := eq35326 X0 X1
       grind)
    | exact resolve eq35326 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq35326
  have eq36127 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35634 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq35634
    | (have j0 := eq35634 X0 (σ X0)
       grind)
    | exact resolve eq35634 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35634
  have eq36282 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36127 X0 X1
       have i₂ := eq3009 X0
       grind)
    | exact superpose eq3009 eq36127
    | (have j0 := eq36127 X0 X1
       grind)
    | exact resolve eq36127 eq3009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36127
  have eq36368 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ X0))) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4325 X0
       have i₂ := eq36282 X0 X1
       grind)
    | exact superpose eq36282 eq4325
    | (have j1 := eq36282 X0 X1
       grind)
    | exact resolve eq4325 eq36282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4325 eq36282
  have eq36528 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36368 X0 X1
       have i₂ := eq3009 X0
       grind)
    | exact superpose eq3009 eq36368
    | (have j0 := eq36368 X0 X1
       grind)
    | exact resolve eq36368 eq3009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36368
  have eq52096 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq32575 X0 X1
       grind)
    | exact superpose eq32575 eq10
    | (have j1 := eq32575 X0 X1
       grind)
    | exact resolve eq10 eq32575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32575
  have eq52294 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52096 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq52096
    | (have j0 := eq52096 X0 X1
       grind)
    | exact resolve eq52096 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52096
  have eq52473 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 X0
       have i₂ := eq52294 X0 X1
       grind)
    | exact superpose eq52294 eq67
    | (have j1 := eq52294 X0 X1
       grind)
    | exact resolve eq67 eq52294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52554 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (σ (k (τ X0) X1)) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3003 X0
       have i₂ := eq52294 (τ X0) X1
       grind)
    | exact superpose eq52294 eq3003
    | (have j1 := eq52294 (τ X0) X1
       grind)
    | exact resolve eq3003 eq52294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3003
  have eq52600 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq52554 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq52554
    | (have j0 := eq52554 X0 X1
       grind)
    | exact resolve eq52554 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52554
  have eq52671 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq52600 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq52600
    | (have j0 := eq52600 X0 X1
       grind)
    | exact resolve eq52600 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq52600
  have eq53087 : ∀ X0 X1 : G, (τ X1) = (τ (M.op X1 X1)) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52671 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq52671
    | (have j0 := eq52671 X1 X1
       grind)
    | exact resolve eq52671 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52671
  have eq53400 : ∀ X0 X1 X2 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2928 X0 X1
       have i₂ := eq53087 X2 X0
       grind)
    | exact superpose eq53087 eq2928
    | (have j0 := eq2928 X0 X1
       have j1 := eq53087 (τ X0) X1
       grind)
    | (have r₁ := eq2928 X1 X1
       have r₂ := eq53087 X0 X1
       grind)
    | exact resolve eq2928 eq53087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2928 eq53087
  have eq53558 : ∀ X0 X1 X2 : G, (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq53400 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53400
  have eq55940 : ∀ X0 : G, (M.op X0 (τ X0)) ≠ (M.op X0 (τ X0)) ∨ (k X0 (τ X0)) = (M.op X0 (τ X0)) := by
    intro X0
    first
    | (have j0 := eq53558 X0 X0 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53558
  have eq55941 : ∀ X0 : G, (k X0 (τ X0)) = (M.op X0 (τ X0)) := by
    intro X0
    first
    | (have j0 := eq55940 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55940
  have eq56708 : ∀ X0 : G, (k X0 (τ (τ (σ X0)))) = (τ (M.op (σ X0) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq30 X0 (τ (σ X0))
       have i₂ := eq55941 (σ X0)
       grind)
    | exact superpose eq55941 eq30
    | exact resolve eq30 eq55941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq56789 : ∀ X0 : G, (k X0 (τ X0)) = (τ (M.op (σ X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq56708 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq56708
    | exact resolve eq56708 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56708
  have eq56851 : ∀ X0 : G, (M.op X0 (τ X0)) = (τ (M.op (σ X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq56789 X0
       have i₂ := eq55941 X0
       grind)
    | exact superpose eq55941 eq56789
    | exact resolve eq56789 eq55941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55941 eq56789
  have eq58460 : ∀ X0 : G, (M.op (σ X0) X0) = (σ (M.op X0 (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) X0)
       have i₂ := eq56851 X0
       grind)
    | exact superpose eq56851 eq11
    | exact resolve eq11 eq56851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56851
  have eq69007 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = X0 ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq52473 X0 X2
       grind)
    | exact superpose eq52473 eq9
    | (have j1 := eq52473 X0 X2
       grind)
    | exact resolve eq9 eq52473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52473
  have eq73687 : ∀ X0 X1 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X0 X1
       have i₂ := eq69007 X0 X1 X2
       grind)
    | exact superpose eq69007 eq67
    | (have j1 := eq69007 X0 X1 X2
       grind)
    | exact resolve eq67 eq69007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69007
  have eq74666 : ∀ X0 X1 X2 : G, (M.op (τ (σ X0)) (M.op X0 (M.op X0 X1))) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7277 X0 X1
       have i₂ := eq36528 X0 X2
       grind)
    | exact superpose eq36528 eq7277
    | (have j1 := eq36528 X0 X2
       grind)
    | exact resolve eq7277 eq36528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36528
  have eq74779 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74666 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq74666
    | (have j0 := eq74666 X0 X1 X2
       grind)
    | exact resolve eq74666 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74666
  have eq76181 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = X0 ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 x)
       have i₂ := eq74779 X0 x X3
       grind)
    | exact superpose eq74779 eq9
    | (have j1 := eq74779 X0 X1 X3
       grind)
    | exact resolve eq9 eq74779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74779
  have eq76521 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X0 X1
       have i₂ := eq76181 X0 X1 X2
       grind)
    | exact superpose eq76181 eq67
    | (have j1 := eq76181 X0 X1 X2
       grind)
    | exact resolve eq67 eq76181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76181
  have eq82586 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq73687 x X0 y
       grind)
    | exact superpose eq73687 eq16
    | (have j1 := eq73687 x X0 x
       grind)
    | exact resolve eq16 eq73687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73687
  have eq83820 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op x X0) ∨ (M.op x x) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq82586 X0
       have i₂ := eq76521 x X1 y
       grind)
    | exact superpose eq76521 eq82586
    | (have j0 := eq82586 X0
       have j1 := eq76521 x X0 x
       grind)
    | exact resolve eq82586 eq76521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76521
  have eq83826 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op x X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq82586 X0
       have i₂ := eq34351 y x
       grind)
    | exact superpose eq34351 eq82586
    | (have j0 := eq82586 X0
       have j1 := eq34351 X0 x
       grind)
    | (have r₁ := eq82586 X0
       have r₂ := eq34351 y x
       grind)
    | exact resolve eq82586 eq34351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34351 eq82586
  have eq83829 : ∀ X0 : G, x = (M.op x x) ∨ (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq83826 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83826
  have eq83835 : ∀ X0 X1 : G, (M.op x x) = (M.op x X0) ∨ (M.op x x) = (M.op x X1) := by
    intro X0 X1
    first
    | (have j0 := eq83820 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83820
  have eq83896 : ∀ X0 : G, x = (M.op x (M.op x x)) ∨ (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq67 x x
       have i₂ := eq83829 X0
       grind)
    | exact superpose eq83829 eq67
    | (have j1 := eq83829 X0
       grind)
    | exact resolve eq67 eq83829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85558 : x ≠ (M.op x x) ∨ (M.op x x) = (M.op x (M.op x x)) := by
    first
    | (have j0 := eq83896 (M.op x x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83896
  have eq85562 : (M.op x x) = (M.op x (M.op x x)) := by
    first
    | (have j1 := eq83829 (M.op x x)
       grind)
    | (have r₁ := eq85558
       have r₂ := eq83829 x
       grind)
    | exact resolve eq85558 eq83829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83829 eq85558
  have eq85618 : x = (M.op (τ (M.op (σ x) (σ (M.op x x)))) (M.op x x)) := by
    first
    | (have i₁ := eq7277 x x
       have i₂ := eq85562
       grind)
    | exact superpose eq85562 eq7277
    | exact resolve eq7277 eq85562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7277 eq85562
  have eq89010 : ∀ X0 : G, (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq83835 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83835
  have eq89011 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq89010 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89010
  have eq89022 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq89011 X1
       have i₂ := eq89011 X0
       grind)
    | (have i₁ := eq89011 X0
       have i₂ := eq89011 x
       grind)
    | exact superpose eq89011 eq89011
    | exact resolve eq89011 eq89011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89118 : ∀ X0 X1 : G, (σ (k x X1)) = (M.op (σ x) (σ X1)) ∨ x = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52294 x X1
       have i₂ := eq89011 X0
       grind)
    | (have i₁ := eq52294 x X1
       have i₂ := eq89011 x
       grind)
    | exact superpose eq89011 eq52294
    | (have j0 := eq52294 x X1
       grind)
    | exact resolve eq52294 eq89011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52294
  have eq89302 : ∀ X0 : G, (σ (M.op x x)) = (k (σ x) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq32406 x X0
       have i₂ := eq89011 (τ X0)
       grind)
    | exact superpose eq89011 eq32406
    | (have j0 := eq32406 x x
       grind)
    | exact resolve eq32406 eq89011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32406
  have eq89310 : (σ (M.op x x)) = (M.op (σ x) x) := by
    first
    | (have i₁ := eq58460 x
       have i₂ := eq89011 (τ x)
       grind)
    | exact superpose eq89011 eq58460
    | exact resolve eq58460 eq89011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89314 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq89302 X0
       have i₂ := eq89310
       grind)
    | exact superpose eq89310 eq89302
    | exact resolve eq89302 eq89310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89302
  have eq90664 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) x) := by
    intro X0
    first
    | (have i₁ := eq58460 x
       have i₂ := eq89022 (τ x) X0
       grind)
    | (have i₁ := eq58460 x
       have i₂ := eq89022 X0 (τ x)
       grind)
    | exact superpose eq89022 eq58460
    | exact resolve eq58460 eq89022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118190 : ∀ X0 : G, (τ (M.op (σ x) (σ (M.op x x)))) = (M.op x (M.op (τ (M.op (σ x) (σ (M.op x x)))) (τ (M.op (σ (τ (M.op (σ x) (σ (M.op x x))))) (σ (M.op (τ (M.op (σ x) (σ (M.op x x)))) (M.op (τ (M.op (σ x) (σ (M.op x x)))) X0))))))) := by
    intro X0
    first
    | (have i₁ := eq14680 (τ (M.op (σ x) (σ (M.op x x)))) X0 (M.op x x)
       have i₂ := eq85618
       grind)
    | exact superpose eq85618 eq14680
    | exact resolve eq14680 eq85618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14680 eq85618
  have eq118207 : (M.op x x) = (τ (M.op (σ x) (σ (M.op x x)))) := by
    first
    | (have i₁ := eq118190 x
       have i₂ := eq89011 (M.op (τ (M.op (σ x) (σ (M.op x x)))) (τ (M.op (σ (τ (M.op (σ x) (σ (M.op x x))))) (σ (M.op (τ (M.op (σ x) (σ (M.op x x)))) (M.op (τ (M.op (σ x) (σ (M.op x x)))) x))))))
       grind)
    | exact superpose eq89011 eq118190
    | exact resolve eq118190 eq89011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89011 eq118190
  have eq118257 : (M.op x x) = (τ (M.op (σ x) (M.op (σ x) x))) := by
    first
    | (have i₁ := eq118207
       have i₂ := eq89310
       grind)
    | exact superpose eq89310 eq118207
    | exact resolve eq118207 eq89310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118207
  have eq118362 : (σ (M.op x x)) = (M.op (σ x) (M.op (σ x) x)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (M.op (σ x) x))
       have i₂ := eq118257
       grind)
    | exact superpose eq118257 eq11
    | exact resolve eq11 eq118257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118257
  have eq118593 : (M.op (σ x) x) = (M.op (σ x) (M.op (σ x) x)) := by
    first
    | (have i₁ := eq118362
       have i₂ := eq89310
       grind)
    | exact superpose eq89310 eq118362
    | exact resolve eq118362 eq89310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89310 eq118362
  have eq119534 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op (σ x) x)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) X0 x
       have i₂ := eq118593
       grind)
    | exact superpose eq118593 eq9
    | exact resolve eq9 eq118593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118593
  have eq134951 : ∀ X0 : G, x = (M.op x x) ∨ (σ (k x X0)) = (M.op (σ x) x) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq89314 (σ X0)
       grind)
    | exact superpose eq89314 eq15
    | exact resolve eq15 eq89314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89314
  have eq161193 : ∀ X0 X1 : G, (σ (k x X1)) = (M.op (σ x) x) ∨ x = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq89022 X0 x
       have i₂ := eq134951 X1
       grind)
    | exact superpose eq134951 eq89022
    | (have j1 := eq134951 X1
       grind)
    | exact resolve eq89022 eq134951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89022 eq134951
  have eq192800 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq89118 X0 y
       grind)
    | exact superpose eq89118 eq16
    | (have j1 := eq89118 X0 x
       grind)
    | exact resolve eq16 eq89118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89118
  have eq193229 : ∀ X0 : G, (σ (k x y)) ≠ (M.op (σ x) x) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq192800 X0
       have i₂ := eq90664 y
       grind)
    | exact superpose eq90664 eq192800
    | (have j0 := eq192800 X0
       grind)
    | exact resolve eq192800 eq90664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192800
  have eq193397 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq193229 X0
       have j1 := eq161193 X0 x
       grind)
    | (have r₁ := eq193229 X0
       have r₂ := eq161193 X0 y
       grind)
    | exact resolve eq193229 eq161193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161193 eq193229
  have eq193810 : (σ x) = (M.op (σ x) x) := by
    first
    | (have i₁ := eq58460 x
       have i₂ := eq193397 (τ x)
       grind)
    | exact superpose eq193397 eq58460
    | exact resolve eq58460 eq193397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58460 eq193397
  have eq195111 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq119534 X0
       have i₂ := eq193810
       grind)
    | exact superpose eq193810 eq119534
    | exact resolve eq119534 eq193810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119534
  have eq201494 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq67 (σ x) X0
       have i₂ := eq195111 X0
       grind)
    | exact superpose eq195111 eq67
    | exact resolve eq67 eq195111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq195111
  have eq201552 : ∀ X0 : G, (σ (M.op x x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq201494 X0
       have i₂ := eq3009 x
       grind)
    | exact superpose eq3009 eq201494
    | exact resolve eq201494 eq3009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3009 eq201494
  have eq201572 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) x) := by
    intro X0
    first
    | (have i₁ := eq201552 X0
       have i₂ := eq90664 x
       grind)
    | exact superpose eq90664 eq201552
    | exact resolve eq201552 eq90664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201552
  have eq201589 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq201572 X0
       have i₂ := eq193810
       grind)
    | exact superpose eq193810 eq201572
    | exact resolve eq201572 eq193810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201572
  have eq201669 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq201589 (σ y)
       grind)
    | exact superpose eq201589 eq16
    | exact resolve eq16 eq201589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201589
  have eq202074 : (σ x) ≠ (M.op (σ x) x) := by
    first
    | (have i₁ := eq201669
       have i₂ := eq90664 y
       grind)
    | exact superpose eq90664 eq201669
    | exact resolve eq201669 eq90664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90664 eq201669
  have eq202209 : False := by grind
  exact eq202209
