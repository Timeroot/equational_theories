import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2949`: `x = ((y ◇ (y ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation2949 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2949 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2949.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29
    | exact resolve eq29 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq111 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41 x y
       grind)
    | exact superpose eq41 eq16
    | (have j1 := eq41 x y
       grind)
    | exact resolve eq16 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq496 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq117 (τ X0) (τ X1)
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq117
    | (have j0 := eq117 (τ X0) (τ X1)
       grind)
    | exact resolve eq117 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq505 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq496 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq496
    | (have j0 := eq496 X0 X1
       grind)
    | exact resolve eq496 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq508 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq505 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq505
    | (have j0 := eq505 X0 X1
       grind)
    | exact resolve eq505 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq510 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq508 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq508
    | (have j0 := eq508 X0 X1
       grind)
    | exact resolve eq508 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq511 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq510 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq510
    | (have j0 := eq510 X0 X1
       grind)
    | exact resolve eq510 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq512 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq511 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq511
    | (have j0 := eq511 X0 X1
       grind)
    | exact resolve eq511 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq513 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq512 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq512
    | (have j0 := eq512 X0 X1
       grind)
    | exact resolve eq512 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq532 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq118 (τ X0) (τ X1)
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq118
    | (have j0 := eq118 (τ X0) (τ X1)
       grind)
    | exact resolve eq118 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq542 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq532 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq532
    | (have j0 := eq532 X0 X1
       grind)
    | exact resolve eq532 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq545 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq542 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq542
    | (have j0 := eq542 X0 X1
       grind)
    | exact resolve eq542 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq547 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq545 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq545
    | (have j0 := eq545 X0 X1
       grind)
    | exact resolve eq545 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq548 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq547 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq547
    | (have j0 := eq547 X0 X1
       grind)
    | exact resolve eq547 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq549 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq548 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq548
    | (have j0 := eq548 X0 X1
       grind)
    | exact resolve eq548 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq550 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq564 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq111
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq111
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq111 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq565 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq564
  have eq3722 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq565
       grind)
    | exact superpose eq565 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq565
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq565
       grind)
    | exact resolve eq13 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3724 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq565
  have eq3725 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq3722
  have eq3726 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3725
       have r₂ := eq3724
       grind)
    | exact resolve eq3725 eq3724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3724 eq3725
  have eq3728 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3726
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3726
    | exact resolve eq3726 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3726
  have eq32281 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq3728
       grind)
    | exact superpose eq3728 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq3728
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq3728
       grind)
    | exact resolve eq12 eq3728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3728
  have eq32282 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq32281
  have eq32285 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32282
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq32282
    | exact resolve eq32282 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32282
  have eq32861 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq32285
       grind)
    | exact superpose eq32285 eq10
    | exact resolve eq10 eq32285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32285
  have eq33021 : y = (k x y) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32861
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq32861
    | exact resolve eq32861 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32861
  have eq33024 : (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq513 x y
       grind)
    | (have r₁ := eq33021
       have r₂ := eq513 x y
       grind)
    | exact resolve eq33021 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513 eq33021
  have eq33354 : (k x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq33024
       grind)
    | exact superpose eq33024 eq10
    | exact resolve eq10 eq33024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33024
  have eq33517 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq33354
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq33354
    | exact resolve eq33354 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33354
  have eq33518 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq550 x y
       grind)
    | (have r₁ := eq33517
       have r₂ := eq550 x y
       grind)
    | exact resolve eq33517 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550 eq33517
  have eq33861 : y ≠ y ∨ x = y ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq33518
       grind)
    | exact superpose eq33518 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq33518
       grind)
    | exact resolve eq13 eq33518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33863 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq33864 : x = y ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq33861
  have eq33865 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq33864
       have r₂ := eq33863
       grind)
    | exact resolve eq33864 eq33863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33864
  have eq34536 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq118 x y
       have i₂ := eq33865
       grind)
    | exact superpose eq33865 eq118
    | (have j0 := eq118 x y
       grind)
    | exact resolve eq118 eq33865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq34580 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq34536
  have eq142005 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34580
       grind)
    | exact superpose eq34580 eq16
    | exact resolve eq16 eq34580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34580
  have eq142112 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq142005
       have i₂ := eq33518
       grind)
    | exact superpose eq33518 eq142005
    | exact resolve eq142005 eq33518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142005
  have eq142115 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq142112
  have eq142116 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq142115
       have r₂ := eq33863
       grind)
    | exact resolve eq142115 eq33863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142115
  have eq142172 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq142116
       grind)
    | exact superpose eq142116 eq16
    | exact resolve eq16 eq142116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142173 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq142116
       grind)
    | exact superpose eq142116 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq142116
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq142116
       grind)
    | exact resolve eq12 eq142116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142116
  have eq142174 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq142173
  have eq142177 : (σ y) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq142174
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq142174
    | exact resolve eq142174 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142174
  have eq142202 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq142172
       have i₂ := eq33518
       grind)
    | exact superpose eq33518 eq142172
    | exact resolve eq142172 eq33518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33518 eq142172
  have eq142206 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq142202
       have r₂ := eq33863
       grind)
    | exact resolve eq142202 eq33863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33863 eq142202
  have eq142250 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq142177
       have i₂ := eq33865
       grind)
    | exact superpose eq33865 eq142177
    | exact resolve eq142177 eq33865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33865
  have eq142288 : (k x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq142177
       grind)
    | exact superpose eq142177 eq10
    | exact resolve eq10 eq142177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142177
  have eq142399 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq142250
  have eq142456 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq142288
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq142288
    | exact resolve eq142288 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142288
  have eq142483 : x = (M.op x y) := by
    first
    | (have r₁ := eq142399
       have r₂ := eq142206
       grind)
    | exact resolve eq142399 eq142206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142206 eq142399
  have eq142484 : y = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq142456
       have r₂ := eq12 x y
       grind)
    | exact resolve eq142456 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142456
  have eq142557 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq117 x y
       have i₂ := eq142484
       grind)
    | exact superpose eq142484 eq117
    | (have j0 := eq117 x y
       grind)
    | exact resolve eq117 eq142484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq142596 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq142557
  have eq144418 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq142596
       grind)
    | exact superpose eq142596 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq142596
       grind)
    | exact resolve eq13 eq142596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144420 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq142596
  have eq144421 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq144418
  have eq144422 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq144421
       have r₂ := eq144420
       grind)
    | exact resolve eq144421 eq144420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144421
  have eq144425 : (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq144422
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq144422
    | exact resolve eq144422 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144422
  have eq144427 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq144425
       have i₂ := eq142484
       grind)
    | exact superpose eq142484 eq144425
    | exact resolve eq144425 eq142484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142484 eq144425
  have eq144428 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq144427
       have r₂ := eq144420
       grind)
    | exact resolve eq144427 eq144420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144420 eq144427
  have eq144521 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq144428
       grind)
    | exact superpose eq144428 eq16
    | exact resolve eq16 eq144428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144428
  have eq144525 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq144521
       have i₂ := eq142483
       grind)
    | exact superpose eq142483 eq144521
    | exact resolve eq144521 eq142483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142483 eq144521
  have eq144526 : False := by grind
  exact eq144526

/-- `Equation2949`: `x = ((y ◇ (y ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pxy_pyx_Equation2949 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2949 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2949.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op X1 X1)) X1) X0) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
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
  have eq52 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X0)) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (M.op X0 X0) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq57 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq65 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq10
    | (have j1 := eq57 X0 X1
       grind)
    | exact resolve eq10 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq159 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq150 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq150
    | (have j0 := eq150 X0 X1
       grind)
    | exact resolve eq150 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq264 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 (M.op (M.op X0 (M.op X0 X0)) X0) X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq299 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X0 (M.op X0 X0)) X0))) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq264 X0 X1
       have i₂ := eq22 (M.op (M.op X0 (M.op X0 X0)) X0)
       grind)
    | exact superpose eq22 eq264
    | exact resolve eq264 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq306 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq299 X0 X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq299
    | exact resolve eq299 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq310 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq306 X0 X1
       have i₂ := eq22 (M.op (M.op X0 (M.op X0 X0)) X0)
       grind)
    | exact superpose eq22 eq306
    | exact resolve eq306 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq314 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq310 X0 X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq310
    | exact resolve eq310 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq1441 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq53
    | (have j0 := eq53 X1 X1
       grind)
    | exact resolve eq53 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1499 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1441 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1441
    | (have j0 := eq1441 (M.op X1 X1) X1
       grind)
    | exact resolve eq1441 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441
  have eq2361 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq159 x y
       grind)
    | exact superpose eq159 eq16
    | (have j1 := eq159 x y
       grind)
    | exact resolve eq16 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq30022 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq2361
       have i₂ := eq1499 y x
       grind)
    | exact superpose eq1499 eq2361
    | (have j1 := eq1499 (M.op x x) x
       grind)
    | (have r₁ := eq2361
       have r₂ := eq1499 y x
       grind)
    | (have r₁ := eq2361
       have r₂ := eq1499 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2361
       have r₂ := eq1499 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2361 eq1499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499 eq2361
  have eq30023 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq30022
  have eq30024 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq30023
  have eq30028 : ∀ X0 : G, (M.op (M.op (M.op x x) x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq30024
       grind)
    | exact superpose eq30024 eq9
    | exact resolve eq9 eq30024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30051 : ∀ X0 : G, (M.op (σ (M.op (M.op x x) x)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq314 x X0
       have i₂ := eq30024
       grind)
    | exact superpose eq30024 eq314
    | exact resolve eq314 eq30024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq30339 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq30028 X0
       have i₂ := eq30024
       grind)
    | exact superpose eq30024 eq30028
    | exact resolve eq30028 eq30024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30024
  have eq30424 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq30339 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30339
  have eq30678 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq30028 X0
       have i₂ := eq30424 x
       grind)
    | exact superpose eq30424 eq30028
    | exact resolve eq30028 eq30424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30028
  have eq30758 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq30678 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30678
  have eq31859 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq30051 X0
       have i₂ := eq30424 x
       grind)
    | exact superpose eq30424 eq30051
    | exact resolve eq30051 eq30424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30051 eq30424
  have eq31970 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq31859 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31859
  have eq32372 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq31970 (σ y)
       grind)
    | exact superpose eq31970 eq16
    | exact resolve eq16 eq31970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31970
  have eq32831 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq32372
       have i₂ := eq30758 y
       grind)
    | exact superpose eq30758 eq32372
    | exact resolve eq32372 eq30758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30758 eq32372
  have eq32832 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq32831
  have eq32833 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq32832
  have eq33122 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq32833
       grind)
    | exact superpose eq32833 eq10
    | exact resolve eq10 eq32833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32833
  have eq33195 : x = y ∨ x = y := by
    first
    | (have i₁ := eq33122
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq33122
    | exact resolve eq33122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33122
  have eq33196 : x = y := by grind
  clear eq33195
  have eq33461 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33196
       grind)
    | exact superpose eq33196 eq16
    | exact resolve eq16 eq33196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33196
  have eq33462 : False := by grind
  exact eq33462

/-- `Equation2949`: `x = ((y ◇ (y ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_x_pyx_Equation2949 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2949 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2949.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op X1 X1)) X1) X0) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
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
  have eq52 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X0)) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (M.op X0 X0) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq57 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq65 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq10
    | (have j1 := eq57 X0 X1
       grind)
    | exact resolve eq10 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq214 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq203 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq203
    | (have j0 := eq203 X0 X1
       grind)
    | exact resolve eq203 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq286 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 (M.op (M.op X0 (M.op X0 X0)) X0) X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq323 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X0 (M.op X0 X0)) X0))) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 X1
       have i₂ := eq22 (M.op (M.op X0 (M.op X0 X0)) X0)
       grind)
    | exact superpose eq22 eq286
    | exact resolve eq286 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq332 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq323 X0 X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq323
    | exact resolve eq323 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq336 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq332 X0 X1
       have i₂ := eq22 (M.op (M.op X0 (M.op X0 X0)) X0)
       grind)
    | exact superpose eq22 eq332
    | exact resolve eq332 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq340 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq336 X0 X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq336
    | exact resolve eq336 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq1449 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq53
    | (have j0 := eq53 X1 X1
       grind)
    | exact resolve eq53 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1509 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1449 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1449
    | (have j0 := eq1449 (M.op X1 X1) X1
       grind)
    | exact resolve eq1449 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449
  have eq2460 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq214 x y
       grind)
    | exact superpose eq214 eq16
    | (have j1 := eq214 x y
       grind)
    | exact resolve eq16 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq27212 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq2460
       have i₂ := eq1509 y x
       grind)
    | exact superpose eq1509 eq2460
    | (have j1 := eq1509 (M.op x x) x
       grind)
    | (have r₁ := eq2460
       have r₂ := eq1509 y x
       grind)
    | (have r₁ := eq2460
       have r₂ := eq1509 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2460
       have r₂ := eq1509 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2460 eq1509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1509 eq2460
  have eq27213 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq27212
  have eq27214 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq27213
  have eq27218 : ∀ X0 : G, (M.op (M.op (M.op x x) x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq27214
       grind)
    | exact superpose eq27214 eq9
    | exact resolve eq9 eq27214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27243 : ∀ X0 : G, (M.op (σ (M.op (M.op x x) x)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq340 x X0
       have i₂ := eq27214
       grind)
    | exact superpose eq27214 eq340
    | exact resolve eq340 eq27214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq27838 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq27218 X0
       have i₂ := eq27214
       grind)
    | exact superpose eq27214 eq27218
    | exact resolve eq27218 eq27214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27214
  have eq27920 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq27838 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27838
  have eq28176 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq27218 X0
       have i₂ := eq27920 x
       grind)
    | exact superpose eq27920 eq27218
    | exact resolve eq27218 eq27920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27218
  have eq28253 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq28176 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28176
  have eq29519 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq27243 X0
       have i₂ := eq27920 x
       grind)
    | exact superpose eq27920 eq27243
    | exact resolve eq27243 eq27920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27243 eq27920
  have eq29624 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq29519 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29519
  have eq30043 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq29624 (σ y)
       grind)
    | exact superpose eq29624 eq16
    | exact resolve eq16 eq29624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29624
  have eq30569 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq30043
       have i₂ := eq28253 y
       grind)
    | exact superpose eq28253 eq30043
    | exact resolve eq30043 eq28253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28253 eq30043
  have eq30570 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq30569
  have eq30571 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq30570
  have eq30904 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq30571
       grind)
    | exact superpose eq30571 eq10
    | exact resolve eq10 eq30571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30571
  have eq30976 : x = y ∨ x = y := by
    first
    | (have i₁ := eq30904
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30904
    | exact resolve eq30904 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30904
  have eq30977 : x = y := by grind
  clear eq30976
  have eq31288 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30977
       grind)
    | exact superpose eq30977 eq16
    | exact resolve eq16 eq30977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30977
  have eq31289 : False := by grind
  exact eq31289

/-- `Equation2949`: `x = ((y ◇ (y ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxy_pxx_pyx_Equation2949 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2949 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2949.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op X1 X1)) X1) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
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
  have eq52 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X0)) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (M.op X0 X0) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq57 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq65 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq10
    | (have j1 := eq57 X0 X1
       grind)
    | exact resolve eq10 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq261 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq250 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq250
    | (have j0 := eq250 X0 X1
       grind)
    | exact resolve eq250 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq309 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 (M.op (M.op X0 (M.op X0 X0)) X0) X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq350 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X0 (M.op X0 X0)) X0))) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq309 X0 X1
       have i₂ := eq22 (M.op (M.op X0 (M.op X0 X0)) X0)
       grind)
    | exact superpose eq22 eq309
    | exact resolve eq309 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq357 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq350 X0 X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq350
    | exact resolve eq350 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq361 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X0 (M.op X0 X0)) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq357 X0 X1
       have i₂ := eq22 (M.op (M.op X0 (M.op X0 X0)) X0)
       grind)
    | exact superpose eq22 eq357
    | exact resolve eq357 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq365 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq361 X0 X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq361
    | exact resolve eq361 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq1550 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq53
    | (have j0 := eq53 X1 X1
       grind)
    | exact resolve eq53 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1614 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1550 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1550
    | (have j0 := eq1550 (M.op X1 X1) X1
       grind)
    | exact resolve eq1550 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550
  have eq2508 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq261 x y
       grind)
    | exact superpose eq261 eq16
    | (have j1 := eq261 x y
       grind)
    | exact resolve eq16 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq51796 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq2508
       have i₂ := eq1614 y x
       grind)
    | exact superpose eq1614 eq2508
    | (have j1 := eq1614 (M.op x x) x
       grind)
    | (have r₁ := eq2508
       have r₂ := eq1614 y x
       grind)
    | (have r₁ := eq2508
       have r₂ := eq1614 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2508
       have r₂ := eq1614 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2508 eq1614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1614 eq2508
  have eq51797 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq51796
  have eq51798 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq51797
  have eq53391 : ∀ X0 : G, (M.op (M.op (M.op x x) x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq51798
       grind)
    | exact superpose eq51798 eq9
    | exact resolve eq9 eq51798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53418 : ∀ X0 : G, (M.op (σ (M.op (M.op x x) x)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq365 x X0
       have i₂ := eq51798
       grind)
    | exact superpose eq51798 eq365
    | exact resolve eq365 eq51798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq54002 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq53391 X0
       have i₂ := eq51798
       grind)
    | exact superpose eq51798 eq53391
    | exact resolve eq53391 eq51798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51798
  have eq54117 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq54002 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54002
  have eq54667 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq53391 X0
       have i₂ := eq54117 x
       grind)
    | exact superpose eq54117 eq53391
    | exact resolve eq53391 eq54117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53391
  have eq54774 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq54667 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54667
  have eq59527 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq53418 X0
       have i₂ := eq54117 x
       grind)
    | exact superpose eq54117 eq53418
    | exact resolve eq53418 eq54117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53418 eq54117
  have eq59677 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq59527 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59527
  have eq62502 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq59677 (σ y)
       grind)
    | exact superpose eq59677 eq16
    | exact resolve eq16 eq59677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59677
  have eq63466 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq62502
       have i₂ := eq54774 y
       grind)
    | exact superpose eq54774 eq62502
    | exact resolve eq62502 eq54774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54774 eq62502
  have eq63467 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq63466
  have eq63468 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq63467
  have eq64226 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq63468
       grind)
    | exact superpose eq63468 eq10
    | exact resolve eq10 eq63468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63468
  have eq64304 : x = y ∨ x = y := by
    first
    | (have i₁ := eq64226
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq64226
    | exact resolve eq64226 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64226
  have eq64305 : x = y := by grind
  clear eq64304
  have eq66109 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq64305
       grind)
    | exact superpose eq64305 eq16
    | exact resolve eq16 eq64305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64305
  have eq66110 : False := by grind
  exact eq66110

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxx_x_pyx_Equation2994 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
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
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq36 (σ X0)
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq38
    | exact resolve eq38 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq38
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
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
  have eq62 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq102 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq105 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq102 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq102 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq102 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq102 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq286 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq105 (σ X1) (σ X0)
       grind)
    | exact superpose eq105 eq15
    | (have j1 := eq105 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq15 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq105 (τ X1) X0
       grind)
    | exact superpose eq105 eq18
    | (have j1 := eq105 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq105
  have eq9550 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq288 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq288
    | exact resolve eq288 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq9690 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9550 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9550
    | (have j0 := eq9550 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq9550 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9550
  have eq24583 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq286 x y
       grind)
    | exact superpose eq286 eq16
    | (have j1 := eq286 x y
       grind)
    | exact resolve eq16 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq24832 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24583
       have i₂ := eq9690 y x
       grind)
    | exact superpose eq9690 eq24583
    | (have j1 := eq9690 (σ x) (σ y)
       grind)
    | (have r₁ := eq24583
       have r₂ := eq9690 y x
       grind)
    | (have r₁ := eq24583
       have r₂ := eq9690 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq24583
       have r₂ := eq9690 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq24583 eq9690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9690 eq24583
  have eq24833 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq24832
  have eq25425 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24833
       grind)
    | exact superpose eq24833 eq10
    | exact resolve eq10 eq24833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24833
  have eq25489 : x = y ∨ x = y := by
    first
    | (have i₁ := eq25425
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq25425
    | exact resolve eq25425 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25425
  have eq25490 : x = y := by grind
  clear eq25489
  have eq25776 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25490
       grind)
    | exact superpose eq25490 eq16
    | exact resolve eq16 eq25490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25490
  have eq25777 : False := by grind
  exact eq25777

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_x_pyx_Equation2994 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq23 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X0) ≠ (M.op (M.op X0 (M.op X1 X0)) X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 (M.op (M.op X0 (M.op X1 X0)) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 (M.op X1 X0)) X0)
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X0)) X0) X0 X1
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X2 (M.op (M.op X0 (M.op X1 X0)) X0)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X1 (M.op X2 X1)) X1)
       have r₂ := eq9 (M.op (M.op X1 (M.op X2 X1)) X1) X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 X2 : G, (M.op X2 X2) = X2 ∨ (k X2 (M.op (M.op X0 (M.op X1 X0)) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq43 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq61 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 X2 X2
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq62 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq69 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq61 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq72 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq63 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq63 X0 (M.op X0 X0) X2
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq63 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq63 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq73 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq68 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq68 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq68 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq74 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq69 X0 X1 X1
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq69 X0 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq69 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq69 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq101 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq73 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq102 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq101 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq105 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq102 (σ X0)
       grind)
    | exact superpose eq102 eq15
    | exact resolve eq15 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq105 X0
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq105
    | exact resolve eq105 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq135 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 (M.op (M.op X2 (M.op X3 X2)) X2)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq46 X2 X3 X0
       grind)
    | exact superpose eq46 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq46 X2 X3 X0
       grind)
    | (have r₁ := eq12 X2 X1
       have r₂ := eq46 X0 X1 X2
       grind)
    | exact resolve eq12 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq145 : ∀ X0 X1 X2 X3 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 (M.op (M.op X2 (M.op X3 X2)) X2)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq135 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq164 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq102 (τ X0)
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq102
    | exact resolve eq102 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq168 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq164 X0
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq164
    | exact resolve eq164 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq198 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X2 ∨ (k X2 (σ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq74 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq74 eq15
    | (have j1 := eq74 (σ X0) X2 X2
       grind)
    | exact resolve eq15 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq233 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) X1
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq23
    | exact resolve eq23 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 X1 : G, (M.op (M.op (τ (M.op X0 X0)) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (τ X0) X1
       have i₂ := eq168 X0
       grind)
    | exact superpose eq168 eq23
    | exact resolve eq23 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq718 : ∀ X0 X1 X2 : G, (M.op (M.op (τ (M.op (M.op X0 (M.op X1 X0)) X0)) (τ (M.op (M.op X0 (M.op X1 X0)) X0))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq338 (M.op (M.op X0 (M.op X1 X0)) X0) X2
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X0)) X0) X0 X1
       grind)
    | exact superpose eq9 eq338
    | exact resolve eq338 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq721 : ∀ X0 X1 : G, (M.op (M.op (τ (M.op (σ (M.op X0 X0)) (σ X0))) (τ (M.op (σ (M.op X0 X0)) (σ X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq338 (M.op (σ (M.op X0 X0)) (σ X0)) X1
       have i₂ := eq233 X0 (M.op (σ (M.op X0 X0)) (σ X0))
       grind)
    | exact superpose eq233 eq338
    | exact resolve eq338 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq762 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (M.op (σ (M.op X0 X0)) (σ X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq721 X0 X1
       have i₂ := eq168 (M.op (σ (M.op X0 X0)) (σ X0))
       grind)
    | exact superpose eq168 eq721
    | exact resolve eq721 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq765 : ∀ X0 X1 X2 : G, (M.op (τ (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op (M.op X0 (M.op X1 X0)) X0))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq718 X0 X1 X2
       have i₂ := eq168 (M.op (M.op X0 (M.op X1 X0)) X0)
       grind)
    | exact superpose eq168 eq718
    | exact resolve eq718 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq718
  have eq779 : ∀ X0 X1 : G, (M.op (τ (M.op (σ (M.op X0 X0)) (σ X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq762 X0 X1
       have i₂ := eq233 X0 (M.op (σ (M.op X0 X0)) (σ X0))
       grind)
    | exact superpose eq233 eq762
    | exact resolve eq762 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq782 : ∀ X0 X1 X2 : G, (M.op (τ (M.op (M.op X0 (M.op X1 X0)) X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq765 X0 X1 X2
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X0)) X0) X0 X1
       grind)
    | exact superpose eq9 eq765
    | exact resolve eq765 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq978 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq72 X0 X0 X2
       grind)
    | exact superpose eq72 eq23
    | (have j1 := eq72 X0 X1 X2
       grind)
    | exact resolve eq23 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq1526 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq978 X0 X2 (τ X1)
       grind)
    | exact superpose eq978 eq17
    | (have j1 := eq978 X0 X2 X2
       grind)
    | exact resolve eq17 eq978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq3468 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) ≠ X0 ∨ (k X0 (M.op (M.op X1 (M.op X2 X1)) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq145 X0 X1 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq3469 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 (M.op X2 X1)) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq3468 X0 X1 X2
       grind)
    | (have r₁ := eq3468 X0 X1 X2
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq3468 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3468
  have eq3509 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3469 X1 X0 (τ (M.op (M.op x (M.op x x)) x))
       have i₂ := eq782 x x X0
       grind)
    | exact superpose eq782 eq3469
    | exact resolve eq3469 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782 eq3469
  have eq3790 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3509 X0 X1
       have i₂ := eq72 X0 X0 X2
       grind)
    | exact superpose eq72 eq3509
    | (have j1 := eq72 X0 X1 X2
       grind)
    | exact resolve eq3509 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq3509
  have eq7424 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3790 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3790
  have eq7924 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ X0) X1) ∨ (σ (k X2 X1)) = (M.op (σ X1) (σ X2)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq198 X1 X2 X0
       grind)
    | exact superpose eq198 eq22
    | (have j1 := eq198 X1 X2 X0
       grind)
    | exact resolve eq22 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq198
  have eq121948 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1526 X1 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1526
    | (have j0 := eq1526 X1 X1 X2
       grind)
    | exact resolve eq1526 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526
  have eq123032 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq121948 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq121948
    | (have j0 := eq121948 X0 X1 X2
       grind)
    | exact resolve eq121948 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121948
  have eq124656 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (σ (k X2 X1)) = (σ (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7424 X0 X1
       have i₂ := eq123032 X2 X1 X0
       grind)
    | exact superpose eq123032 eq7424
    | (have j0 := eq7424 X0 X1
       have j1 := eq123032 X2 X1 X2
       grind)
    | (have r₁ := eq7424 X2 X1
       have r₂ := eq123032 X0 X1 X2
       grind)
    | exact resolve eq7424 eq123032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7424 eq123032
  have eq124944 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (σ (k X2 X1)) = (σ (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq124656 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124656
  have eq217997 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (τ X0) = (k (τ X0) x) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq7924 X0 x y
       grind)
    | exact superpose eq7924 eq16
    | (have j1 := eq7924 X0 x x
       grind)
    | exact resolve eq16 eq7924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7924
  have eq218833 : ∀ X0 : G, (τ X0) = (k (τ X0) x) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq217997 X0
       have j1 := eq124944 (τ X0) x x
       grind)
    | (have r₁ := eq217997 X0
       have r₂ := eq124944 X0 x y
       grind)
    | exact resolve eq217997 eq124944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124944 eq217997
  have eq219214 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17 X0 x
       have i₂ := eq218833 X0
       grind)
    | exact superpose eq218833 eq17
    | (have j1 := eq218833 X0
       grind)
    | exact resolve eq17 eq218833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq218833
  have eq219754 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq219214 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq219214
    | (have j0 := eq219214 X0
       grind)
    | exact resolve eq219214 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219214
  have eq221909 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq102 (σ x)
       have i₂ := eq219754 (σ x)
       grind)
    | exact superpose eq219754 eq102
    | (have j1 := eq219754 (σ x)
       grind)
    | exact resolve eq102 eq219754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq219754
  have eq222319 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq221909
  have eq222505 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq222319
       have i₂ := eq114 x
       grind)
    | exact superpose eq114 eq222319
    | exact resolve eq222319 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222319
  have eq224329 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq233 x X0
       have i₂ := eq222505
       grind)
    | exact superpose eq222505 eq233
    | exact resolve eq233 eq222505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq224335 : ∀ X0 : G, (M.op (τ (M.op (σ x) (σ x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq779 x X0
       have i₂ := eq222505
       grind)
    | exact superpose eq222505 eq779
    | exact resolve eq779 eq222505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq224365 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq222505
       grind)
    | exact superpose eq222505 eq10
    | exact resolve eq10 eq222505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224569 : x = (M.op x x) := by
    first
    | (have i₁ := eq224365
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq224365
    | exact resolve eq224365 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224365
  have eq224591 : ∀ X0 : G, (M.op (τ (σ (M.op x x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq224335 X0
       have i₂ := eq114 x
       grind)
    | exact superpose eq114 eq224335
    | exact resolve eq224335 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224335
  have eq224594 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq224329 X0
       have i₂ := eq114 x
       grind)
    | exact superpose eq114 eq224329
    | exact resolve eq224329 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq224329
  have eq224621 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq224591 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq224591
    | exact resolve eq224591 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224591
  have eq224624 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq224594 X0
       have i₂ := eq222505
       grind)
    | exact superpose eq222505 eq224594
    | exact resolve eq224594 eq222505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222505 eq224594
  have eq224642 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq224621 X0
       have i₂ := eq224569
       grind)
    | exact superpose eq224569 eq224621
    | exact resolve eq224621 eq224569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224569 eq224621
  have eq231926 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq224624 (σ y)
       grind)
    | exact superpose eq224624 eq16
    | exact resolve eq16 eq224624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224624
  have eq232402 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq231926
       have i₂ := eq224642 y
       grind)
    | exact superpose eq224642 eq231926
    | exact resolve eq231926 eq224642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224642 eq231926
  have eq232403 : False := by grind
  exact eq232403

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_x_pxx_pyx_Equation2994 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
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
  have eq20 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq44 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X0)) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X0 X2) ∨ (k X1 X0) = X1 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq48 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq52 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq57 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq59 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq52 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq52
    | (have j0 := eq52 X0
       grind)
    | exact resolve eq52 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq71 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57
    | exact resolve eq57 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq172 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44 x y
       grind)
    | exact superpose eq44 eq16
    | (have j1 := eq44 x y
       grind)
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq819 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq172 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq172
    | (have j0 := eq172 (τ X0)
       grind)
    | exact resolve eq172 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq832 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq819 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq819
    | (have j0 := eq819 X0
       grind)
    | exact resolve eq819 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq839 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq832 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq832
    | (have j0 := eq832 X0
       grind)
    | exact resolve eq832 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq857 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq839 (τ X0)
       have i₂ := eq71 X0 X0
       grind)
    | exact superpose eq71 eq839
    | (have j0 := eq839 (τ X0)
       grind)
    | exact resolve eq839 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1431 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq59
    | exact resolve eq59 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq1452 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1431 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1431
    | (have j0 := eq1431 X0
       grind)
    | exact resolve eq1431 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1431
  have eq3759 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k X0 x) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq258
       have i₂ := eq50 x X0 y
       grind)
    | exact superpose eq50 eq258
    | (have j1 := eq50 x X0 y
       grind)
    | (have r₁ := eq258
       have r₂ := eq50 (σ (M.op x y)) x (σ (k y x))
       grind)
    | (have r₁ := eq258
       have r₂ := eq50 (σ (k y x)) x (σ (M.op x y))
       grind)
    | exact resolve eq258 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq258
  have eq3763 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 x) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq3759 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3759
  have eq47764 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq18 X0 x
       have i₂ := eq3763 (τ X0)
       grind)
    | exact superpose eq3763 eq18
    | exact resolve eq18 eq3763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3763
  have eq47827 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq47764 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq47764
    | exact resolve eq47764 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47764
  have eq47851 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq47827 X0
       have j1 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq47827 X0
       have r₂ := eq12 X0 (σ x)
       grind)
    | exact resolve eq47827 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47827
  have eq47909 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq839 (σ x)
       have i₂ := eq47851 (σ x)
       grind)
    | exact superpose eq47851 eq839
    | (have j0 := eq839 (σ x)
       grind)
    | (have r₁ := eq839 (σ x)
       have r₂ := eq47851 (σ x)
       grind)
    | exact resolve eq839 eq47851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq47910 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq857 (σ x)
       have i₂ := eq47851 (σ x)
       grind)
    | exact superpose eq47851 eq857
    | (have j0 := eq857 (σ x)
       grind)
    | exact resolve eq857 eq47851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47851
  have eq48028 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq47910
  have eq48029 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq47909
  have eq48075 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq48028
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq48028
    | exact resolve eq48028 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48028
  have eq48356 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq20 x X0
       have i₂ := eq48075
       grind)
    | exact superpose eq48075 eq20
    | exact resolve eq20 eq48075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48075
  have eq55478 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq20 x X0
       have i₂ := eq48356 x
       grind)
    | exact superpose eq48356 eq20
    | exact resolve eq20 eq48356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48356
  have eq59459 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq20 (σ x) X0
       have i₂ := eq48029
       grind)
    | exact superpose eq48029 eq20
    | exact resolve eq20 eq48029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48029
  have eq71013 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq20 (σ x) X0
       have i₂ := eq59459 (σ x)
       grind)
    | exact superpose eq59459 eq20
    | exact resolve eq20 eq59459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq59459
  have eq71714 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq71013 (σ y)
       grind)
    | exact superpose eq71013 eq16
    | exact resolve eq16 eq71013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71013
  have eq72740 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq71714
       have i₂ := eq55478 y
       grind)
    | exact superpose eq55478 eq71714
    | exact resolve eq71714 eq55478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55478 eq71714
  have eq72741 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq72740
  have eq72742 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq72741
  have eq73346 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq72742
       grind)
    | exact superpose eq72742 eq10
    | exact resolve eq10 eq72742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72742
  have eq73451 : x = y ∨ x = y := by
    first
    | (have i₁ := eq73346
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq73346
    | exact resolve eq73346 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73346
  have eq73452 : x = y := by grind
  clear eq73451
  have eq74356 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq73452
       grind)
    | exact superpose eq73452 eq16
    | exact resolve eq16 eq73452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73452
  have eq74997 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq74356
       have i₂ := eq33 x
       grind)
    | exact superpose eq33 eq74356
    | (have j1 := eq33 x
       grind)
    | exact resolve eq74356 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq95648 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq74997
       have i₂ := eq1452 x
       grind)
    | exact superpose eq1452 eq74997
    | (have j1 := eq1452 (σ x)
       grind)
    | (have r₁ := eq74997
       have r₂ := eq1452 x
       grind)
    | exact resolve eq74997 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452 eq74997
  have eq95650 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq95648
  have eq96455 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq95650
       grind)
    | exact superpose eq95650 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq95650
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq95650
       grind)
    | exact resolve eq12 eq95650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95650
  have eq96517 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq96455 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96455
  have eq98094 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq857 (σ x)
       have i₂ := eq96517 (σ x)
       grind)
    | exact superpose eq96517 eq857
    | (have j0 := eq857 (σ x)
       grind)
    | exact resolve eq857 eq96517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857 eq96517
  have eq98258 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by grind
  clear eq98094
  have eq98312 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq98258
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq98258
    | exact resolve eq98258 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98258
  have eq98313 : x = (M.op x x) := by grind
  clear eq98312
  have eq99371 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq98313
       grind)
    | exact superpose eq98313 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq98313
       grind)
    | exact resolve eq12 eq98313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99433 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq99371 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99371
  have eq101002 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq172 x
       have i₂ := eq99433 x
       grind)
    | exact superpose eq99433 eq172
    | (have j0 := eq172 x
       grind)
    | exact resolve eq172 eq99433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq99433
  have eq101183 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq101002
  have eq116181 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq74356
       have i₂ := eq101183
       grind)
    | exact superpose eq101183 eq74356
    | exact resolve eq74356 eq101183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74356 eq101183
  have eq116272 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq116181
       have i₂ := eq98313
       grind)
    | exact superpose eq98313 eq116181
    | exact resolve eq116181 eq98313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98313 eq116181
  have eq116273 : False := by grind
  exact eq116273

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation2994 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq44 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq48 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq152 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44 x y
       grind)
    | exact superpose eq44 eq16
    | (have j1 := eq44 x y
       grind)
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq1013 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq48
    | exact resolve eq48 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq1042 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1013 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1013
    | (have j0 := eq1013 X0 X1
       grind)
    | exact resolve eq1013 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq2137 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq152
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq152
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq152
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq152
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq152 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq2138 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq2137
  have eq31663 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq2138
       grind)
    | exact superpose eq2138 eq16
    | exact resolve eq16 eq2138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31665 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq2138
       grind)
    | exact superpose eq2138 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2138
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2138
       grind)
    | exact resolve eq13 eq2138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2138
  have eq31681 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq31665
  have eq31682 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq31681
  have eq31684 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq31682
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq31682
    | exact resolve eq31682 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31682
  have eq309435 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1042 x y
       have i₂ := eq31684
       grind)
    | exact superpose eq31684 eq1042
    | (have j0 := eq1042 x y
       grind)
    | exact resolve eq1042 eq31684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq309439 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq31684
       grind)
    | exact superpose eq31684 eq10
    | exact resolve eq10 eq31684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31684
  have eq309631 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq309435
  have eq309673 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq309439
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq309439
    | exact resolve eq309439 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309439
  have eq309674 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq309631
       have r₂ := eq31663
       grind)
    | exact resolve eq309631 eq31663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31663 eq309631
  have eq309677 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 y (k y x)
       grind)
    | (have r₁ := eq309673
       have r₂ := eq13 y x
       grind)
    | exact resolve eq309673 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309673
  have eq315430 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq157 x y
       have i₂ := eq309677
       grind)
    | exact superpose eq309677 eq157
    | (have j0 := eq157 x y
       grind)
    | exact resolve eq157 eq309677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq309677
  have eq315447 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq315430
  have eq315448 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq315447
  have eq316546 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq315448
       grind)
    | exact superpose eq315448 eq16
    | exact resolve eq16 eq315448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315448
  have eq317428 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq316546
       have i₂ := eq309674
       grind)
    | exact superpose eq309674 eq316546
    | exact resolve eq316546 eq309674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309674 eq316546
  have eq317429 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq317428
  have eq317430 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq317429
  have eq318127 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq317430
       grind)
    | exact superpose eq317430 eq10
    | exact resolve eq10 eq317430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317430
  have eq318352 : x = y ∨ x = y := by
    first
    | (have i₁ := eq318127
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq318127
    | exact resolve eq318127 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318127
  have eq318353 : x = y := by grind
  clear eq318352
  have eq319589 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq318353
       grind)
    | exact superpose eq318353 eq16
    | exact resolve eq16 eq318353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318353
  have eq319590 : False := by grind
  exact eq319590

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pxy_pyx_Equation2994 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X0)) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (M.op X0 X0) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq50 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 X0 X1
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq71 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq10
    | (have j1 := eq50 X0 X1
       grind)
    | exact resolve eq10 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq194 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq183 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq183
    | (have j0 := eq183 X0 X1
       grind)
    | exact resolve eq183 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq275 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq71 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq24 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq24 eq71
    | exact resolve eq71 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq308 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq275 X0 X1
       have i₂ := eq22 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq22 eq275
    | exact resolve eq275 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq315 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq308 X0 X1
       have i₂ := eq24 X0 (M.op (M.op X0 X0) X0)
       grind)
    | (have i₁ := eq308 X0 X1
       have i₂ := eq24 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq24 eq308
    | exact resolve eq308 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq1678 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45
    | (have j0 := eq45 X1 X1
       grind)
    | exact resolve eq45 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq1761 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1678 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1678
    | (have j0 := eq1678 (M.op X1 X1) X1
       grind)
    | exact resolve eq1678 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1678
  have eq2940 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq194 x y
       grind)
    | exact superpose eq194 eq16
    | (have j1 := eq194 x y
       grind)
    | exact resolve eq16 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq30957 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq2940
       have i₂ := eq1761 y x
       grind)
    | exact superpose eq1761 eq2940
    | (have j1 := eq1761 (M.op x x) x
       grind)
    | (have r₁ := eq2940
       have r₂ := eq1761 y x
       grind)
    | (have r₁ := eq2940
       have r₂ := eq1761 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2940
       have r₂ := eq1761 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2940 eq1761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1761 eq2940
  have eq30958 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq30957
  have eq30959 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq30958
  have eq30965 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq24 x X0
       have i₂ := eq30959
       grind)
    | exact superpose eq30959 eq24
    | exact resolve eq24 eq30959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30959
  have eq31407 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq24 x X0
       have i₂ := eq30965 x
       grind)
    | exact superpose eq30965 eq24
    | exact resolve eq24 eq30965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq31412 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq315 x X0
       have i₂ := eq30965 x
       grind)
    | exact superpose eq30965 eq315
    | exact resolve eq315 eq30965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315 eq30965
  have eq32327 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq31412 (σ y)
       grind)
    | exact superpose eq31412 eq16
    | exact resolve eq16 eq31412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31412
  have eq35715 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq32327
       have i₂ := eq31407 y
       grind)
    | exact superpose eq31407 eq32327
    | exact resolve eq32327 eq31407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31407 eq32327
  have eq35716 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq35715
  have eq35717 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq35716
  have eq35973 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq35717
       grind)
    | exact superpose eq35717 eq10
    | exact resolve eq10 eq35717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35717
  have eq36054 : x = y ∨ x = y := by
    first
    | (have i₁ := eq35973
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq35973
    | exact resolve eq35973 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35973
  have eq36055 : x = y := by grind
  clear eq36054
  have eq36294 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36055
       grind)
    | exact superpose eq36055 eq16
    | exact resolve eq16 eq36055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36055
  have eq36295 : False := by grind
  exact eq36295

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_x_pyx_Equation2994 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X0)) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (M.op X0 X0) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq50 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 X0 X1
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq71 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq10
    | (have j1 := eq50 X0 X1
       grind)
    | exact resolve eq10 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq237 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq226 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq226
    | (have j0 := eq226 X0 X1
       grind)
    | exact resolve eq226 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq277 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq71 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq24 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq24 eq71
    | exact resolve eq71 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq310 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq277 X0 X1
       have i₂ := eq22 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq22 eq277
    | exact resolve eq277 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq317 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq310 X0 X1
       have i₂ := eq24 X0 (M.op (M.op X0 X0) X0)
       grind)
    | (have i₁ := eq310 X0 X1
       have i₂ := eq24 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq24 eq310
    | exact resolve eq310 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq1901 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45
    | (have j0 := eq45 X1 X1
       grind)
    | exact resolve eq45 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq1989 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1901 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1901
    | (have j0 := eq1901 (M.op X1 X1) X1
       grind)
    | exact resolve eq1901 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1901
  have eq3357 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq237 x y
       grind)
    | exact superpose eq237 eq16
    | (have j1 := eq237 x y
       grind)
    | exact resolve eq16 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq32340 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq3357
       have i₂ := eq1989 y x
       grind)
    | exact superpose eq1989 eq3357
    | (have j1 := eq1989 (M.op x x) x
       grind)
    | (have r₁ := eq3357
       have r₂ := eq1989 y x
       grind)
    | (have r₁ := eq3357
       have r₂ := eq1989 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq3357
       have r₂ := eq1989 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq3357 eq1989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1989 eq3357
  have eq32341 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq32340
  have eq32342 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq32341
  have eq32348 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq24 x X0
       have i₂ := eq32342
       grind)
    | exact superpose eq32342 eq24
    | exact resolve eq24 eq32342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32342
  have eq32785 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq24 x X0
       have i₂ := eq32348 x
       grind)
    | exact superpose eq32348 eq24
    | exact resolve eq24 eq32348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq32790 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq317 x X0
       have i₂ := eq32348 x
       grind)
    | exact superpose eq32348 eq317
    | exact resolve eq317 eq32348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317 eq32348
  have eq34115 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq32790 (σ y)
       grind)
    | exact superpose eq32790 eq16
    | exact resolve eq16 eq32790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32790
  have eq36626 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq34115
       have i₂ := eq32785 y
       grind)
    | exact superpose eq32785 eq34115
    | exact resolve eq34115 eq32785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32785 eq34115
  have eq36627 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq36626
  have eq36628 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq36627
  have eq36955 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq36628
       grind)
    | exact superpose eq36628 eq10
    | exact resolve eq10 eq36628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36628
  have eq37037 : x = y ∨ x = y := by
    first
    | (have i₁ := eq36955
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq36955
    | exact resolve eq36955 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36955
  have eq37038 : x = y := by grind
  clear eq37037
  have eq37435 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq37038
       grind)
    | exact superpose eq37038 eq16
    | exact resolve eq16 eq37038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37038
  have eq37436 : False := by grind
  exact eq37436

/-- `Equation4268`: `x ◇ (x ◇ x) = x ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_y_pxx_pxx_pxy_Equation4268 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4268 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4268.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
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
  have eq24 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X2
       have i₂ := eq9 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1
       have i₂ := eq9 X1 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq38 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq38 (σ X0)
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq38 (τ X0)
       grind)
    | exact superpose eq38 eq19
    | exact resolve eq19 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq42
    | exact resolve eq42 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq40
    | exact resolve eq40 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq47 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq43
    | exact resolve eq43 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq43
  have eq51 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq73 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq79 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq65
    | (have j0 := eq65 X0 X1
       grind)
    | exact resolve eq65 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq79
    | (have j0 := eq79 X0 X1
       grind)
    | exact resolve eq79 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq139 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq140 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq12
    | exact resolve eq12 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) (σ X0) X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq24
    | exact resolve eq24 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq139 X0
       have j1 := eq140 X0 (σ (M.op X0 X0))
       grind)
    | (have r₁ := eq139 X0
       have r₂ := eq140 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq139 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq140
  have eq149 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq147 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq147
    | exact resolve eq147 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq151 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 X2) ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X2)) ∨ (M.op X0 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 X0 (M.op X0 X1)
       have i₂ := eq24 X0 X1 X2
       grind)
    | (have i₁ := eq74 X0 (M.op X0 X2)
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq74
    | (have j0 := eq74 X0 (M.op X0 X2)
       grind)
    | (have r₁ := eq74 X0 (M.op X0 (M.op X0 X2))
       have r₂ := eq24 X0 (M.op X0 X2) X2
       grind)
    | (have r₁ := eq74 X0 (M.op X0 (M.op X0 X1))
       have r₂ := eq24 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq74 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq237 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq75
    | (have j0 := eq75 (σ X0) (σ (k X0 X1))
       grind)
    | exact resolve eq75 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq270 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq267 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq267 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq267 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq267 X0 X1
       have r₂ := eq14 X0 (M.op X0 X1)
       grind)
    | exact resolve eq267 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq285 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq237 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq237
    | (have j0 := eq237 X0 X1
       grind)
    | exact resolve eq237 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq293 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq285 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq285
    | (have j0 := eq285 X0 X1
       grind)
    | exact resolve eq285 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq309 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (M.op X0 X0))
       have i₂ := eq149 X0
       grind)
    | exact superpose eq149 eq10
    | exact resolve eq10 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq310 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq309 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq309
    | exact resolve eq309 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq484 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq485 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq484 X0 X1
       have j1 := eq293 X0 X1
       grind)
    | (have r₁ := eq484 X0 X1
       have r₂ := eq293 X0 X1
       grind)
    | (have r₁ := eq484 X0 X1
       have r₂ := eq293 X0 (k X0 X1)
       grind)
    | exact resolve eq484 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293 eq484
  have eq554 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq270 X0 (τ X1)
       grind)
    | exact superpose eq270 eq19
    | (have j1 := eq270 X0 (τ X1)
       grind)
    | exact resolve eq19 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq567 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq310 X0
       have i₂ := eq270 X0 X1
       grind)
    | (have i₁ := eq310 X0
       have i₂ := eq270 X0 (M.op X0 X0)
       grind)
    | exact superpose eq270 eq310
    | (have j1 := eq270 X1 X0
       grind)
    | exact resolve eq310 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq787 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq567 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq859 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq787 X0 (M.op X0 X2)
       have i₂ := eq24 X0 X2 X1
       grind)
    | (have i₁ := eq787 X0 (M.op X0 X2)
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq787
    | (have j0 := eq787 X0 (M.op X0 X2)
       grind)
    | (have r₁ := eq787 X0 (M.op X0 (M.op X0 X2))
       have r₂ := eq24 X0 (M.op X0 X2) X2
       grind)
    | (have r₁ := eq787 X0 (M.op X0 (M.op X0 X1))
       have r₂ := eq24 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq787 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq1411 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ (k X0 X1))) = (M.op (σ X0) (M.op (σ X0) X2)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (σ X0) X2 (σ X1)
       have i₂ := eq485 X0 X1
       grind)
    | exact superpose eq485 eq24
    | (have j1 := eq485 X0 X1
       grind)
    | exact resolve eq24 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1449 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq485 X1 X0
       grind)
    | (have i₁ := eq10 X1
       have i₂ := eq485 X0 X1
       grind)
    | exact superpose eq485 eq10
    | (have j1 := eq485 X1 X0
       grind)
    | exact resolve eq10 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1456 : ∀ X0 X1 X2 : G, (τ (k X1 (σ X0))) = (k (τ X1) (M.op X2 X2)) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X1 (M.op X2 X2)
       have i₂ := eq485 X2 X0
       grind)
    | (have i₁ := eq23 X0 X1
       have i₂ := eq485 X0 X1
       grind)
    | exact superpose eq485 eq23
    | (have j1 := eq485 X2 X0
       grind)
    | exact resolve eq23 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq1478 : ∀ X0 X1 X2 : G, (k (τ X1) X0) = (k (τ X1) (M.op X2 X2)) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1456 X0 X1 X2
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq1456
    | (have j0 := eq1456 X0 X1 X2
       grind)
    | exact resolve eq1456 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1456
  have eq1485 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1449 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1449
    | (have j0 := eq1449 X0 X1
       grind)
    | exact resolve eq1449 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449
  have eq3039 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1485 y x
       grind)
    | exact superpose eq1485 eq16
    | (have j1 := eq1485 y x
       grind)
    | exact resolve eq16 eq1485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3420 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3039
       have i₂ := eq270 x y
       grind)
    | exact superpose eq270 eq3039
    | (have j1 := eq270 x y
       grind)
    | exact resolve eq3039 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq3039
  have eq3427 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq3420
  have eq3428 : y = (M.op x x) := by grind
  clear eq3427
  have eq3504 : ∀ X0 : G, y ≠ (M.op x X0) ∨ y = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x x
       have i₂ := eq3428
       grind)
    | exact superpose eq3428 eq12
    | exact resolve eq12 eq3428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3507 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq143 x X0
       have i₂ := eq3428
       grind)
    | exact superpose eq3428 eq143
    | exact resolve eq143 eq3428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq3514 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq24 x X0 x
       have i₂ := eq3428
       grind)
    | exact superpose eq3428 eq24
    | exact resolve eq24 eq3428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4627 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq151 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq4722 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k x X0))) ∨ (M.op x x) = X0 := by
    intro X0
    first
    | (have i₁ := eq3507 (σ X0)
       have i₂ := eq1485 X0 x
       grind)
    | exact superpose eq1485 eq3507
    | (have j1 := eq1485 X0 x
       grind)
    | exact resolve eq3507 eq1485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1485
  have eq4789 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq4722 X0
       have i₂ := eq3428
       grind)
    | exact superpose eq3428 eq4722
    | (have j0 := eq4722 X0
       grind)
    | exact resolve eq4722 eq3428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4722
  have eq19090 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq554 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq554
    | exact resolve eq554 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq19461 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19090 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq19090
    | (have j0 := eq19090 X0 X1
       grind)
    | exact resolve eq19090 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19090
  have eq44445 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (k (τ X0) X1)) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq149 (τ X0)
       have i₂ := eq1478 X1 X0 (τ X0)
       grind)
    | (have i₁ := eq149 (τ X1)
       have i₂ := eq1478 (M.op (τ X1) (τ X1)) X1 x
       grind)
    | exact superpose eq1478 eq149
    | (have j1 := eq1478 X1 X1 (τ X0)
       grind)
    | exact resolve eq149 eq1478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq1478
  have eq44601 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k (τ X0) X1)) ∨ (σ (k (τ X0) X1)) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq44445 X0 X1
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq44445
    | (have j0 := eq44445 X0 X1
       grind)
    | exact resolve eq44445 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44445
  have eq44757 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq44601 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq44601
    | (have j0 := eq44601 X0 X1
       grind)
    | exact resolve eq44601 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44601
  have eq44833 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq44757 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq44757
    | (have j0 := eq44757 X0 X1
       grind)
    | exact resolve eq44757 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44757
  have eq44888 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq44833 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq44833
    | (have j0 := eq44833 X0 X1
       grind)
    | exact resolve eq44833 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq44833
  have eq50081 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 ∨ (M.op x x) = X0 := by
    intro X0
    first
    | (have i₁ := eq4789 X0
       have i₂ := eq19461 X0 x
       grind)
    | exact superpose eq19461 eq4789
    | (have j0 := eq4789 X0
       have j1 := eq19461 X0 x
       grind)
    | exact resolve eq4789 eq19461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4789 eq19461
  have eq50262 : ∀ X0 : G, y = X0 ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq50081 X0
       have i₂ := eq3428
       grind)
    | exact superpose eq3428 eq50081
    | (have j0 := eq50081 X0
       grind)
    | exact resolve eq50081 eq3428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50081
  have eq50263 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq50262 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50262
  have eq52890 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) (M.op (σ (τ X0)) X2)) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1411 (τ X0) (τ X1) X2
       have i₂ := eq51 X1 X0
       grind)
    | exact superpose eq51 eq1411
    | (have j0 := eq1411 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq1411 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1411
  have eq53425 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) (M.op (σ (τ X0)) X2)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52890 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq52890
    | (have j0 := eq52890 X0 X1 X2
       grind)
    | exact resolve eq52890 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52890
  have eq53480 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) = (M.op X0 (k X0 X1)) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53425 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq53425
    | (have j0 := eq53425 X0 X1 X2
       grind)
    | exact resolve eq53425 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53425
  have eq53497 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X0 (M.op X0 X2)) = (M.op X0 (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53480 X0 X1 X2
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq53480
    | (have j0 := eq53480 X0 X1 X2
       grind)
    | exact resolve eq53480 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq53480
  have eq53505 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) = (M.op X0 (k X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53497 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq53497
    | (have j0 := eq53497 X0 X1 X2
       grind)
    | exact resolve eq53497 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53497
  have eq53852 : ∀ X0 X1 : G, y ≠ (M.op x (M.op x X0)) ∨ y = (k x (k x X1)) ∨ (M.op x x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3504 (k x X1)
       have i₂ := eq53505 x X1 X0
       grind)
    | exact superpose eq53505 eq3504
    | (have j0 := eq3504 (M.op x X0)
       have j1 := eq53505 x X1 x
       grind)
    | (have r₁ := eq3504 x
       have r₂ := eq53505 x y x
       grind)
    | exact resolve eq3504 eq53505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3504 eq53505
  have eq53874 : ∀ X1 : G, y ≠ (M.op x y) ∨ y = (k x (k x X1)) ∨ (M.op x x) = X1 := by
    intro X1
    first
    | (have i₁ := eq53852 x X1
       have i₂ := eq3514 x
       grind)
    | exact superpose eq3514 eq53852
    | (have j0 := eq53852 x X1
       grind)
    | exact resolve eq53852 eq3514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53852
  have eq53946 : ∀ X1 : G, y ≠ (M.op x y) ∨ y = X1 ∨ y = (k x (k x X1)) := by
    intro X1
    first
    | (have i₁ := eq53874 X1
       have i₂ := eq3428
       grind)
    | exact superpose eq3428 eq53874
    | (have j0 := eq53874 X1
       grind)
    | exact resolve eq53874 eq3428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53874
  have eq62949 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X1) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq44888 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq44888
    | exact resolve eq44888 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63312 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 (σ X1)
       have i₂ := eq44888 (σ X0) X1
       grind)
    | exact superpose eq44888 eq33
    | (have j1 := eq44888 (σ X0) X1
       grind)
    | exact resolve eq33 eq44888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44888
  have eq63390 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63312 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq63312
    | (have j0 := eq63312 X0 X1
       grind)
    | exact resolve eq63312 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63312
  have eq63553 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63390 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq63390
    | (have j0 := eq63390 X0 X1
       grind)
    | exact resolve eq63390 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq63390
  have eq63638 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63553 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq63553
    | (have j0 := eq63553 X0 X1
       grind)
    | exact resolve eq63553 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63553
  have eq63700 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq63638 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq63638
    | (have j0 := eq63638 X0 X1
       grind)
    | exact resolve eq63638 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63638
  have eq65081 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (k X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq310 X1
       have i₂ := eq62949 X0 X1
       grind)
    | exact superpose eq62949 eq310
    | (have j1 := eq62949 X1 X0
       grind)
    | exact resolve eq310 eq62949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq65361 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq62949 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66243 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65361 X0 (M.op X0 X1)
       have i₂ := eq24 X0 X1 X2
       grind)
    | (have i₁ := eq65361 X0 (M.op X0 X2)
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq65361
    | (have j0 := eq65361 X0 (M.op X0 X1)
       grind)
    | exact resolve eq65361 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq65361
  have eq69996 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq65081 X0 (M.op X0 (M.op X0 X1))
       have i₂ := eq4627 X0 X1
       grind)
    | exact superpose eq4627 eq65081
    | (have j1 := eq4627 X0 X1
       grind)
    | exact resolve eq65081 eq4627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4627 eq65081
  have eq70294 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq69996 X0 X1
       have j1 := eq66243 X0 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq69996 X0 X1
       have r₂ := eq66243 X0 X1 x
       grind)
    | exact resolve eq69996 eq66243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66243 eq69996
  have eq70334 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq70294 X0 X1
       have j1 := eq859 X0 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq70294 X0 X1
       have r₂ := eq859 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | (have r₁ := eq70294 X0 X1
       have r₂ := eq859 X0 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq70294 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859 eq70294
  have eq71611 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq70334 (σ x) x
       have i₂ := eq3507 x
       grind)
    | exact superpose eq3507 eq70334
    | exact resolve eq70334 eq3507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3507
  have eq73137 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq33 x (M.op (σ x) (σ y))
       have i₂ := eq71611
       grind)
    | exact superpose eq71611 eq33
    | exact resolve eq33 eq71611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq71611
  have eq120882 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq63700 X1 X0
       have i₂ := eq62949 X0 X1
       grind)
    | exact superpose eq62949 eq63700
    | (have j0 := eq63700 X0 X1
       have j1 := eq62949 X1 X0
       grind)
    | exact resolve eq63700 eq62949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62949 eq63700
  have eq121888 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq120882 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq120882 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq120882 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq120882 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120882
  have eq188298 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op x (M.op x X0))) ∨ y = X0 ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq50263 X0
       have i₂ := eq121888 x (M.op x X0)
       grind)
    | exact superpose eq121888 eq50263
    | (have j0 := eq50263 X0
       have j1 := eq121888 x (M.op x X0)
       grind)
    | exact resolve eq50263 eq121888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50263 eq121888
  have eq188511 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = X0 ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq188298 X0
       have i₂ := eq3514 X0
       grind)
    | exact superpose eq3514 eq188298
    | (have j0 := eq188298 X0
       grind)
    | exact resolve eq188298 eq3514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188298
  have eq188551 : ∀ X0 : G, y = X0 ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq188511 X0
       grind)
    | (have r₁ := eq188511 X0
       have r₂ := eq16
       grind)
    | exact resolve eq188511 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188511
  have eq188562 : ∀ X0 : G, y = (k x (M.op x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq188551 X0
       have i₂ := eq3428
       grind)
    | exact superpose eq3428 eq188551
    | (have j0 := eq188551 (k x (M.op x X0))
       grind)
    | exact resolve eq188551 eq3428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3428 eq188551
  have eq189548 : ∀ X0 : G, y = (M.op x (M.op x X0)) ∨ y = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq70334 x X0
       have i₂ := eq188562 (M.op x X0)
       grind)
    | exact superpose eq188562 eq70334
    | (have j1 := eq188562 (M.op x (M.op x X0))
       grind)
    | exact resolve eq70334 eq188562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70334 eq188562
  have eq189619 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq189548 X0
       have i₂ := eq3514 X0
       grind)
    | exact superpose eq3514 eq189548
    | (have j0 := eq189548 y
       grind)
    | exact resolve eq189548 eq3514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3514 eq189548
  have eq190730 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq189619 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189619
  have eq190731 : y = (M.op x y) := by grind
  clear eq190730
  have eq191681 : ∀ X0 : G, y ≠ y ∨ y = X0 ∨ y = (k x (k x X0)) := by
    intro X0
    first
    | (have i₁ := eq53946 X0
       have i₂ := eq190731
       grind)
    | exact superpose eq190731 eq53946
    | (have j0 := eq53946 X0
       grind)
    | (have r₁ := eq53946 x
       have r₂ := eq190731
       grind)
    | exact resolve eq53946 eq190731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53946
  have eq191727 : ∀ X0 : G, y = (k x (k x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq191681 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191681
  have eq196880 : y = (k x (τ (M.op (σ x) (σ y)))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq191727 (τ (M.op (σ x) (σ y)))
       have i₂ := eq73137
       grind)
    | exact superpose eq73137 eq191727
    | (have j0 := eq191727 (k x (τ (M.op (σ x) (σ y))))
       grind)
    | exact resolve eq191727 eq73137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191727
  have eq197054 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq196880
       have i₂ := eq73137
       grind)
    | exact superpose eq73137 eq196880
    | exact resolve eq196880 eq73137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73137 eq196880
  have eq197055 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq197054
  have eq198376 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq197055
       grind)
    | exact superpose eq197055 eq11
    | exact resolve eq11 eq197055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197055
  have eq201184 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq198376
       grind)
    | exact superpose eq198376 eq16
    | exact resolve eq16 eq198376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198376
  have eq201302 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq201184
       have i₂ := eq190731
       grind)
    | exact superpose eq190731 eq201184
    | exact resolve eq201184 eq190731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190731 eq201184
  have eq201303 : False := by grind
  exact eq201303

/-- `Equation4268`: `x ◇ (x ◇ x) = x ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_y_pxx_y_pxy_Equation4268 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4268 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4268.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
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
  have eq24 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X2
       have i₂ := eq9 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1
       have i₂ := eq9 X1 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq38 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq38 (σ X0)
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq38 (τ X0)
       grind)
    | exact superpose eq38 eq19
    | exact resolve eq19 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq42
    | exact resolve eq42 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq40
    | exact resolve eq40 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq47 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq43
    | exact resolve eq43 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq43
  have eq51 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq73 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq79 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq65
    | (have j0 := eq65 X0 X1
       grind)
    | exact resolve eq65 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq79
    | (have j0 := eq79 X0 X1
       grind)
    | exact resolve eq79 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq139 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq140 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq12
    | exact resolve eq12 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) (σ X0) X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq24
    | exact resolve eq24 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq139 X0
       have j1 := eq140 X0 (σ (M.op X0 X0))
       grind)
    | (have r₁ := eq139 X0
       have r₂ := eq140 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq139 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq140
  have eq149 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq147 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq147
    | exact resolve eq147 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq151 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 X2) ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X2)) ∨ (M.op X0 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 X0 (M.op X0 X1)
       have i₂ := eq24 X0 X1 X2
       grind)
    | (have i₁ := eq74 X0 (M.op X0 X2)
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq74
    | (have j0 := eq74 X0 (M.op X0 X2)
       grind)
    | (have r₁ := eq74 X0 (M.op X0 (M.op X0 X2))
       have r₂ := eq24 X0 (M.op X0 X2) X2
       grind)
    | (have r₁ := eq74 X0 (M.op X0 (M.op X0 X1))
       have r₂ := eq24 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq74 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq237 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq75
    | (have j0 := eq75 (σ X0) (σ (k X0 X1))
       grind)
    | exact resolve eq75 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq270 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq267 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq267 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq267 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq267 X0 X1
       have r₂ := eq14 X0 (M.op X0 X1)
       grind)
    | exact resolve eq267 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq285 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq237 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq237
    | (have j0 := eq237 X0 X1
       grind)
    | exact resolve eq237 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq293 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq285 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq285
    | (have j0 := eq285 X0 X1
       grind)
    | exact resolve eq285 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq309 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (M.op X0 X0))
       have i₂ := eq149 X0
       grind)
    | exact superpose eq149 eq10
    | exact resolve eq10 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq310 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq309 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq309
    | exact resolve eq309 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq484 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq485 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq484 X0 X1
       have j1 := eq293 X0 X1
       grind)
    | (have r₁ := eq484 X0 X1
       have r₂ := eq293 X0 X1
       grind)
    | (have r₁ := eq484 X0 X1
       have r₂ := eq293 X0 (k X0 X1)
       grind)
    | exact resolve eq484 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293 eq484
  have eq554 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq270 X0 (τ X1)
       grind)
    | exact superpose eq270 eq19
    | (have j1 := eq270 X0 (τ X1)
       grind)
    | exact resolve eq19 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq567 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq310 X0
       have i₂ := eq270 X0 X1
       grind)
    | (have i₁ := eq310 X0
       have i₂ := eq270 X0 (M.op X0 X0)
       grind)
    | exact superpose eq270 eq310
    | (have j1 := eq270 X1 X0
       grind)
    | exact resolve eq310 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq787 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq567 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq859 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq787 X0 (M.op X0 X2)
       have i₂ := eq24 X0 X2 X1
       grind)
    | (have i₁ := eq787 X0 (M.op X0 X2)
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq787
    | (have j0 := eq787 X0 (M.op X0 X2)
       grind)
    | (have r₁ := eq787 X0 (M.op X0 (M.op X0 X2))
       have r₂ := eq24 X0 (M.op X0 X2) X2
       grind)
    | (have r₁ := eq787 X0 (M.op X0 (M.op X0 X1))
       have r₂ := eq24 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq787 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq1411 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ (k X0 X1))) = (M.op (σ X0) (M.op (σ X0) X2)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (σ X0) X2 (σ X1)
       have i₂ := eq485 X0 X1
       grind)
    | exact superpose eq485 eq24
    | (have j1 := eq485 X0 X1
       grind)
    | exact resolve eq24 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1449 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq485 X1 X0
       grind)
    | (have i₁ := eq10 X1
       have i₂ := eq485 X0 X1
       grind)
    | exact superpose eq485 eq10
    | (have j1 := eq485 X1 X0
       grind)
    | exact resolve eq10 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1456 : ∀ X0 X1 X2 : G, (τ (k X1 (σ X0))) = (k (τ X1) (M.op X2 X2)) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X1 (M.op X2 X2)
       have i₂ := eq485 X2 X0
       grind)
    | (have i₁ := eq23 X0 X1
       have i₂ := eq485 X0 X1
       grind)
    | exact superpose eq485 eq23
    | (have j1 := eq485 X2 X0
       grind)
    | exact resolve eq23 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq1478 : ∀ X0 X1 X2 : G, (k (τ X1) X0) = (k (τ X1) (M.op X2 X2)) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1456 X0 X1 X2
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq1456
    | (have j0 := eq1456 X0 X1 X2
       grind)
    | exact resolve eq1456 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1456
  have eq1485 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1449 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1449
    | (have j0 := eq1449 X0 X1
       grind)
    | exact resolve eq1449 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449
  have eq3039 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1485 y x
       grind)
    | exact superpose eq1485 eq16
    | (have j1 := eq1485 y x
       grind)
    | exact resolve eq16 eq1485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3420 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3039
       have i₂ := eq270 x y
       grind)
    | exact superpose eq270 eq3039
    | (have j1 := eq270 x y
       grind)
    | exact resolve eq3039 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq3039
  have eq3427 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq3420
  have eq3428 : y = (M.op x x) := by grind
  clear eq3427
  have eq3504 : ∀ X0 : G, y ≠ (M.op x X0) ∨ y = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x x
       have i₂ := eq3428
       grind)
    | exact superpose eq3428 eq12
    | exact resolve eq12 eq3428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3507 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq143 x X0
       have i₂ := eq3428
       grind)
    | exact superpose eq3428 eq143
    | exact resolve eq143 eq3428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq3514 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq24 x X0 x
       have i₂ := eq3428
       grind)
    | exact superpose eq3428 eq24
    | exact resolve eq24 eq3428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4627 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq151 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq4722 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k x X0))) ∨ (M.op x x) = X0 := by
    intro X0
    first
    | (have i₁ := eq3507 (σ X0)
       have i₂ := eq1485 X0 x
       grind)
    | exact superpose eq1485 eq3507
    | (have j1 := eq1485 X0 x
       grind)
    | exact resolve eq3507 eq1485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1485
  have eq4789 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq4722 X0
       have i₂ := eq3428
       grind)
    | exact superpose eq3428 eq4722
    | (have j0 := eq4722 X0
       grind)
    | exact resolve eq4722 eq3428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4722
  have eq19090 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq554 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq554
    | exact resolve eq554 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq19461 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19090 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq19090
    | (have j0 := eq19090 X0 X1
       grind)
    | exact resolve eq19090 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19090
  have eq44445 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (k (τ X0) X1)) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq149 (τ X0)
       have i₂ := eq1478 X1 X0 (τ X0)
       grind)
    | (have i₁ := eq149 (τ X1)
       have i₂ := eq1478 (M.op (τ X1) (τ X1)) X1 x
       grind)
    | exact superpose eq1478 eq149
    | (have j1 := eq1478 X1 X1 (τ X0)
       grind)
    | exact resolve eq149 eq1478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq1478
  have eq44601 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k (τ X0) X1)) ∨ (σ (k (τ X0) X1)) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq44445 X0 X1
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq44445
    | (have j0 := eq44445 X0 X1
       grind)
    | exact resolve eq44445 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44445
  have eq44757 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq44601 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq44601
    | (have j0 := eq44601 X0 X1
       grind)
    | exact resolve eq44601 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44601
  have eq44833 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq44757 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq44757
    | (have j0 := eq44757 X0 X1
       grind)
    | exact resolve eq44757 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44757
  have eq44888 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq44833 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq44833
    | (have j0 := eq44833 X0 X1
       grind)
    | exact resolve eq44833 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq44833
  have eq50081 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 ∨ (M.op x x) = X0 := by
    intro X0
    first
    | (have i₁ := eq4789 X0
       have i₂ := eq19461 X0 x
       grind)
    | exact superpose eq19461 eq4789
    | (have j0 := eq4789 X0
       have j1 := eq19461 X0 x
       grind)
    | exact resolve eq4789 eq19461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4789 eq19461
  have eq50262 : ∀ X0 : G, y = X0 ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq50081 X0
       have i₂ := eq3428
       grind)
    | exact superpose eq3428 eq50081
    | (have j0 := eq50081 X0
       grind)
    | exact resolve eq50081 eq3428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50081
  have eq50263 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq50262 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50262
  have eq52890 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) (M.op (σ (τ X0)) X2)) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1411 (τ X0) (τ X1) X2
       have i₂ := eq51 X1 X0
       grind)
    | exact superpose eq51 eq1411
    | (have j0 := eq1411 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq1411 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1411
  have eq53425 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) (M.op (σ (τ X0)) X2)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52890 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq52890
    | (have j0 := eq52890 X0 X1 X2
       grind)
    | exact resolve eq52890 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52890
  have eq53480 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) = (M.op X0 (k X0 X1)) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53425 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq53425
    | (have j0 := eq53425 X0 X1 X2
       grind)
    | exact resolve eq53425 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53425
  have eq53497 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X0 (M.op X0 X2)) = (M.op X0 (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53480 X0 X1 X2
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq53480
    | (have j0 := eq53480 X0 X1 X2
       grind)
    | exact resolve eq53480 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq53480
  have eq53505 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) = (M.op X0 (k X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53497 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq53497
    | (have j0 := eq53497 X0 X1 X2
       grind)
    | exact resolve eq53497 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53497
  have eq53852 : ∀ X0 X1 : G, y ≠ (M.op x (M.op x X0)) ∨ y = (k x (k x X1)) ∨ (M.op x x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3504 (k x X1)
       have i₂ := eq53505 x X1 X0
       grind)
    | exact superpose eq53505 eq3504
    | (have j0 := eq3504 (M.op x X0)
       have j1 := eq53505 x X1 x
       grind)
    | (have r₁ := eq3504 x
       have r₂ := eq53505 x y x
       grind)
    | exact resolve eq3504 eq53505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3504 eq53505
  have eq53874 : ∀ X1 : G, y ≠ (M.op x y) ∨ y = (k x (k x X1)) ∨ (M.op x x) = X1 := by
    intro X1
    first
    | (have i₁ := eq53852 x X1
       have i₂ := eq3514 x
       grind)
    | exact superpose eq3514 eq53852
    | (have j0 := eq53852 x X1
       grind)
    | exact resolve eq53852 eq3514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53852
  have eq53946 : ∀ X1 : G, y ≠ (M.op x y) ∨ y = X1 ∨ y = (k x (k x X1)) := by
    intro X1
    first
    | (have i₁ := eq53874 X1
       have i₂ := eq3428
       grind)
    | exact superpose eq3428 eq53874
    | (have j0 := eq53874 X1
       grind)
    | exact resolve eq53874 eq3428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53874
  have eq62949 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X1) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq44888 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq44888
    | exact resolve eq44888 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63312 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 (σ X1)
       have i₂ := eq44888 (σ X0) X1
       grind)
    | exact superpose eq44888 eq33
    | (have j1 := eq44888 (σ X0) X1
       grind)
    | exact resolve eq33 eq44888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44888
  have eq63390 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63312 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq63312
    | (have j0 := eq63312 X0 X1
       grind)
    | exact resolve eq63312 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63312
  have eq63553 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63390 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq63390
    | (have j0 := eq63390 X0 X1
       grind)
    | exact resolve eq63390 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq63390
  have eq63638 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63553 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq63553
    | (have j0 := eq63553 X0 X1
       grind)
    | exact resolve eq63553 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63553
  have eq63700 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq63638 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq63638
    | (have j0 := eq63638 X0 X1
       grind)
    | exact resolve eq63638 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63638
  have eq65081 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (k X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq310 X1
       have i₂ := eq62949 X0 X1
       grind)
    | exact superpose eq62949 eq310
    | (have j1 := eq62949 X1 X0
       grind)
    | exact resolve eq310 eq62949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq65361 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq62949 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66243 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65361 X0 (M.op X0 X1)
       have i₂ := eq24 X0 X1 X2
       grind)
    | (have i₁ := eq65361 X0 (M.op X0 X2)
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq65361
    | (have j0 := eq65361 X0 (M.op X0 X1)
       grind)
    | exact resolve eq65361 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq65361
  have eq69996 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq65081 X0 (M.op X0 (M.op X0 X1))
       have i₂ := eq4627 X0 X1
       grind)
    | exact superpose eq4627 eq65081
    | (have j1 := eq4627 X0 X1
       grind)
    | exact resolve eq65081 eq4627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4627 eq65081
  have eq70294 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq69996 X0 X1
       have j1 := eq66243 X0 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq69996 X0 X1
       have r₂ := eq66243 X0 X1 x
       grind)
    | exact resolve eq69996 eq66243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66243 eq69996
  have eq70334 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq70294 X0 X1
       have j1 := eq859 X0 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq70294 X0 X1
       have r₂ := eq859 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | (have r₁ := eq70294 X0 X1
       have r₂ := eq859 X0 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq70294 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859 eq70294
  have eq71611 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq70334 (σ x) x
       have i₂ := eq3507 x
       grind)
    | exact superpose eq3507 eq70334
    | exact resolve eq70334 eq3507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3507
  have eq73137 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq33 x (M.op (σ x) (σ y))
       have i₂ := eq71611
       grind)
    | exact superpose eq71611 eq33
    | exact resolve eq33 eq71611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq71611
  have eq120882 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq63700 X1 X0
       have i₂ := eq62949 X0 X1
       grind)
    | exact superpose eq62949 eq63700
    | (have j0 := eq63700 X0 X1
       have j1 := eq62949 X1 X0
       grind)
    | exact resolve eq63700 eq62949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62949 eq63700
  have eq121888 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq120882 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq120882 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq120882 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq120882 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120882
  have eq188832 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op x (M.op x X0))) ∨ y = X0 ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq50263 X0
       have i₂ := eq121888 x (M.op x X0)
       grind)
    | exact superpose eq121888 eq50263
    | (have j0 := eq50263 X0
       have j1 := eq121888 x (M.op x X0)
       grind)
    | exact resolve eq50263 eq121888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50263 eq121888
  have eq189045 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = X0 ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq188832 X0
       have i₂ := eq3514 X0
       grind)
    | exact superpose eq3514 eq188832
    | (have j0 := eq188832 X0
       grind)
    | exact resolve eq188832 eq3514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188832
  have eq189085 : ∀ X0 : G, y = X0 ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq189045 X0
       grind)
    | (have r₁ := eq189045 X0
       have r₂ := eq16
       grind)
    | exact resolve eq189045 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189045
  have eq189096 : ∀ X0 : G, y = (k x (M.op x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq189085 X0
       have i₂ := eq3428
       grind)
    | exact superpose eq3428 eq189085
    | (have j0 := eq189085 (k x (M.op x X0))
       grind)
    | exact resolve eq189085 eq3428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3428 eq189085
  have eq190082 : ∀ X0 : G, y = (M.op x (M.op x X0)) ∨ y = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq70334 x X0
       have i₂ := eq189096 (M.op x X0)
       grind)
    | exact superpose eq189096 eq70334
    | (have j1 := eq189096 (M.op x (M.op x X0))
       grind)
    | exact resolve eq70334 eq189096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70334 eq189096
  have eq190153 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq190082 X0
       have i₂ := eq3514 X0
       grind)
    | exact superpose eq3514 eq190082
    | (have j0 := eq190082 y
       grind)
    | exact resolve eq190082 eq3514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3514 eq190082
  have eq191264 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq190153 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190153
  have eq191265 : y = (M.op x y) := by grind
  clear eq191264
  have eq192215 : ∀ X0 : G, y ≠ y ∨ y = X0 ∨ y = (k x (k x X0)) := by
    intro X0
    first
    | (have i₁ := eq53946 X0
       have i₂ := eq191265
       grind)
    | exact superpose eq191265 eq53946
    | (have j0 := eq53946 X0
       grind)
    | (have r₁ := eq53946 x
       have r₂ := eq191265
       grind)
    | exact resolve eq53946 eq191265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53946
  have eq192261 : ∀ X0 : G, y = (k x (k x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq192215 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192215
  have eq197414 : y = (k x (τ (M.op (σ x) (σ y)))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq192261 (τ (M.op (σ x) (σ y)))
       have i₂ := eq73137
       grind)
    | exact superpose eq73137 eq192261
    | (have j0 := eq192261 (k x (τ (M.op (σ x) (σ y))))
       grind)
    | exact resolve eq192261 eq73137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192261
  have eq197588 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq197414
       have i₂ := eq73137
       grind)
    | exact superpose eq73137 eq197414
    | exact resolve eq197414 eq73137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73137 eq197414
  have eq197589 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq197588
  have eq198910 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq197589
       grind)
    | exact superpose eq197589 eq11
    | exact resolve eq11 eq197589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197589
  have eq201718 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq198910
       grind)
    | exact superpose eq198910 eq16
    | exact resolve eq16 eq198910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198910
  have eq201836 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq201718
       have i₂ := eq191265
       grind)
    | exact superpose eq191265 eq201718
    | exact resolve eq201718 eq191265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191265 eq201718
  have eq201837 : False := by grind
  exact eq201837

/-- `Equation4268`: `x ◇ (x ◇ x) = x ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pxy_pxx_pxy_Equation4268 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4268 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4268.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq24 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X2
       have i₂ := eq9 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1
       have i₂ := eq9 X1 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, X0 = X2 ∨ X0 = X1 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq14 X0 X1
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | (have j0 := eq14 X1 X1
       have j1 := eq14 X1 X1
       grind)
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq65 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X1 X2)) ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq72 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq61 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq74 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq72 (M.op X0 X1) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq72 (k X0 X1) (M.op X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq72 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq72 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq75 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X1 X2)) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq65 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq65 X0 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq65 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq77 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq63 (M.op X0 X0) X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq63 X0 (M.op X0 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq63 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq63 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq78 : ∀ X0 X1 X2 : G, X0 = X2 ∨ X0 = X1 ∨ (M.op X1 X2) = (k X1 X2) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq59 X0 X1 X2
       have j1 := eq12 X1 X2
       grind)
    | (have r₁ := eq59 (M.op X0 X0) X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq59 X0 X1 (M.op X0 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq59 (M.op X0 X0) X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq59 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq80 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       have j1 := eq74 X1 X0
       grind)
    | (have r₁ := eq77 X1 X1
       have r₂ := eq74 (k X1 X1) X1
       grind)
    | (have r₁ := eq77 X0 X1
       have r₂ := eq74 X0 (k X1 X0)
       grind)
    | (have r₁ := eq77 X0 X1
       have r₂ := eq74 X0 X1
       grind)
    | exact resolve eq77 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq81 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq78 X0 X1 X2
       have j1 := eq74 X1 X2
       grind)
    | (have r₁ := eq78 X0 X1 X1
       have r₂ := eq74 X0 X1
       grind)
    | (have r₁ := eq78 X1 X1 X0
       have r₂ := eq74 X0 X1
       grind)
    | (have r₁ := eq78 X0 X1 X2
       have r₂ := eq74 X0 X1
       grind)
    | exact resolve eq78 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq83 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq74 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq111 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq83 (σ X0)
       grind)
    | exact superpose eq83 eq15
    | exact resolve eq15 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq83 (τ X0)
       grind)
    | exact superpose eq83 eq19
    | exact resolve eq19 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq115 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq115
    | exact resolve eq115 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq120 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq111 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq111
    | exact resolve eq111 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq122 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq116 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq116
    | exact resolve eq116 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq135 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq80 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq139 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq135 X0 (M.op X0 X2)
       have i₂ := eq24 X0 X2 X1
       grind)
    | (have i₁ := eq135 X0 (M.op X0 X2)
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq135
    | (have j0 := eq135 X0 (M.op X0 X2)
       grind)
    | (have r₁ := eq135 X0 (M.op X0 (M.op X0 X2))
       have r₂ := eq24 X0 (M.op X0 X2) X2
       grind)
    | (have r₁ := eq135 X0 (M.op X0 (M.op X0 X1))
       have r₂ := eq24 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq135 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq159 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq83 (τ X0)
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq83
    | exact resolve eq83 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq162 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq159 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq159
    | exact resolve eq159 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq206 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (M.op (σ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq75 (σ X1) (σ X0) X2
       grind)
    | exact superpose eq75 eq15
    | (have j1 := eq75 (σ X1) (σ X0) X2
       grind)
    | exact resolve eq15 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) (σ X0) X1
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq24
    | exact resolve eq24 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = X2 ∨ (M.op (σ X0) X2) = (k (σ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq81 (σ X1) (σ X0) X2
       grind)
    | exact superpose eq81 eq15
    | (have j1 := eq81 (σ X1) (σ X0) X2
       grind)
    | exact resolve eq15 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq310 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq311 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq310 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq329 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) X1
       have i₂ := eq162 X0
       grind)
    | exact superpose eq162 eq14
    | (have j0 := eq14 (τ X0) X1
       grind)
    | exact resolve eq14 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq162 X0
       grind)
    | exact superpose eq162 eq12
    | (have j0 := eq12 (τ X0) X1
       grind)
    | exact resolve eq12 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq329 X0 X1
       have j1 := eq331 X0 X1
       grind)
    | (have r₁ := eq329 X0 X1
       have r₂ := eq331 X0 X1
       grind)
    | (have r₁ := eq329 X0 (τ (M.op (M.op X0 X0) (M.op X0 X0)))
       have r₂ := eq331 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq329 X0 (τ X0)
       have r₂ := eq331 X0 X1
       grind)
    | exact resolve eq329 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329 eq331
  have eq422 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq311 (σ X0) (σ X1)
       grind)
    | exact superpose eq311 eq15
    | (have j1 := eq311 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq311 X0 (τ X1)
       grind)
    | exact superpose eq311 eq19
    | (have j1 := eq311 X0 (τ X1)
       grind)
    | exact resolve eq19 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq422 X0 X1
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq422
    | (have j0 := eq422 X0 X1
       grind)
    | exact resolve eq422 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq523 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq10
    | (have j1 := eq66 X0 X1
       grind)
    | exact resolve eq10 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq595 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq523 X0 X1
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq523
    | (have j0 := eq523 X0 X1
       grind)
    | exact resolve eq523 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq661 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq595 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq595
    | (have j0 := eq595 X0 X1
       grind)
    | exact resolve eq595 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq715 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq661 X0 X1
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq661
    | (have j0 := eq661 X0 X1
       grind)
    | exact resolve eq661 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq3833 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq715 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq715
    | (have j0 := eq715 (τ X0) X1
       grind)
    | exact resolve eq715 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3869 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (σ (k X0 X2)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X2 ∨ (M.op (σ X0) (σ X2)) = (k (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq715 X0 X2
       have i₂ := eq75 (σ X2) (σ X0) X1
       grind)
    | exact superpose eq75 eq715
    | (have j0 := eq715 X0 X2
       have j1 := eq75 (σ X2) (σ X0) X2
       grind)
    | exact resolve eq715 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq715
  have eq4058 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (σ (k X0 X2)) ∨ (M.op X0 X0) = X2 ∨ (M.op (σ X0) (σ X2)) = (k (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3869 X0 X1 X2
       have j1 := eq221 X0 (σ X2)
       grind)
    | (have r₁ := eq3869 X0 X1 X2
       have r₂ := eq221 X0 X1
       grind)
    | exact resolve eq3869 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3869
  have eq4077 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3833 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq3833
    | (have j0 := eq3833 X0 X1
       grind)
    | exact resolve eq3833 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3833
  have eq4134 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (σ (k X0 X2)) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (M.op X0 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4058 X0 X1 X2
       have i₂ := eq15 X0 X2
       grind)
    | exact superpose eq15 eq4058
    | (have j0 := eq4058 X0 X1 X2
       grind)
    | exact resolve eq4058 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4058
  have eq4146 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4077 X0 X1
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq4077
    | (have j0 := eq4077 X0 X1
       grind)
    | exact resolve eq4077 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq4077
  have eq4184 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4146 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq4146 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq4146 X0 (τ X0)
       have r₂ := eq12 (τ X0) X1
       grind)
    | (have r₁ := eq4146 X0 (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))
       have r₂ := eq12 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact resolve eq4146 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4146
  have eq4210 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4184 X0 X1
       have i₂ := eq162 X0
       grind)
    | exact superpose eq162 eq4184
    | (have j0 := eq4184 X0 X1
       grind)
    | exact resolve eq4184 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq4184
  have eq4330 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq4210 (σ X0) X1
       grind)
    | exact superpose eq4210 eq15
    | (have j1 := eq4210 (σ X0) X1
       grind)
    | exact resolve eq15 eq4210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4352 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4330 X0 X1
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq4330
    | (have j0 := eq4330 X0 X1
       grind)
    | exact resolve eq4330 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq4330
  have eq4373 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4352 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq4352
    | (have j0 := eq4352 X0 X1
       grind)
    | exact resolve eq4352 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4352
  have eq5141 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (M.op (σ X0) X2)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq206 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq5293 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4373 x y
       grind)
    | exact superpose eq4373 eq16
    | (have j1 := eq4373 x y
       grind)
    | exact resolve eq16 eq4373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5644 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq248 X0 X2 (σ X1)
       grind)
    | exact superpose eq248 eq15
    | (have j1 := eq248 X0 X1 (σ X2)
       grind)
    | exact resolve eq15 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq5821 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5293
       have i₂ := eq311 x y
       grind)
    | exact superpose eq311 eq5293
    | (have j1 := eq311 x y
       grind)
    | exact resolve eq5293 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5293
  have eq5826 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq5821
  have eq5827 : y = (M.op x x) := by grind
  clear eq5826
  have eq6255 : ∀ X0 : G, x ≠ y ∨ (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x X0
       have i₂ := eq5827
       grind)
    | exact superpose eq5827 eq12
    | (have j0 := eq12 x X0
       grind)
    | exact resolve eq12 eq5827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6257 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq226 x X0
       have i₂ := eq5827
       grind)
    | exact superpose eq5827 eq226
    | exact resolve eq226 eq5827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq6264 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq24 x X0 x
       have i₂ := eq5827
       grind)
    | exact superpose eq5827 eq24
    | exact resolve eq24 eq5827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq9070 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k x X0))) ∨ (M.op x x) = X0 := by
    intro X0
    first
    | (have i₁ := eq6257 (σ X0)
       have i₂ := eq4373 x X0
       grind)
    | exact superpose eq4373 eq6257
    | (have j1 := eq4373 x X0
       grind)
    | exact resolve eq6257 eq4373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4373
  have eq9127 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq9070 X0
       have i₂ := eq5827
       grind)
    | exact superpose eq5827 eq9070
    | (have j0 := eq9070 X0
       grind)
    | exact resolve eq9070 eq5827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9070
  have eq26242 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq427 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq427
    | exact resolve eq427 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq26645 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26242 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq26242
    | (have j0 := eq26242 X0 X1
       grind)
    | exact resolve eq26242 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26242
  have eq31088 : ∀ X0 X1 X2 : G, (σ X0) = (σ X1) ∨ (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq446 X2 X1
       have i₂ := eq26645 X0 X2
       grind)
    | (have i₁ := eq446 X0 X1
       have i₂ := eq26645 (M.op X0 X0) X1
       grind)
    | exact superpose eq26645 eq446
    | (have j0 := eq446 X2 X1
       have j1 := eq26645 X0 X2
       grind)
    | exact resolve eq446 eq26645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq32553 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq139 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq32681 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq32553 (σ x) x
       have i₂ := eq6257 x
       grind)
    | exact superpose eq6257 eq32553
    | exact resolve eq32553 eq6257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6257 eq32553
  have eq33649 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq33 x (M.op (σ x) (σ y))
       have i₂ := eq32681
       grind)
    | exact superpose eq32681 eq33
    | exact resolve eq33 eq32681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq32681
  have eq39513 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq221 x X0
       have i₂ := eq5827
       grind)
    | exact superpose eq5827 eq221
    | (have j0 := eq221 x X0
       grind)
    | exact resolve eq221 eq5827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq66016 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 ∨ (M.op x x) = X0 := by
    intro X0
    first
    | (have i₁ := eq9127 X0
       have i₂ := eq26645 X0 x
       grind)
    | exact superpose eq26645 eq9127
    | (have j0 := eq9127 X0
       have j1 := eq26645 X0 x
       grind)
    | exact resolve eq9127 eq26645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9127
  have eq66193 : ∀ X0 : G, y = X0 ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq66016 X0
       have i₂ := eq5827
       grind)
    | exact superpose eq5827 eq66016
    | (have j0 := eq66016 X0
       grind)
    | exact resolve eq66016 eq5827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66016
  have eq66194 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq66193 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66193
  have eq88819 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X2)) ≠ (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5141 X1 X0 X2
       have i₂ := eq26645 X0 X1
       grind)
    | exact superpose eq26645 eq5141
    | (have j1 := eq26645 X1 X0
       grind)
    | exact resolve eq5141 eq26645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5141 eq26645
  have eq159212 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq5644 x X0 y
       grind)
    | exact superpose eq5644 eq16
    | (have j1 := eq5644 x X0 X0
       grind)
    | exact resolve eq16 eq5644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5644
  have eq159224 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq159212 X0
       have j1 := eq31088 X0 y x
       grind)
    | (have r₁ := eq159212 X0
       have r₂ := eq31088 (M.op x y) (k x y) x
       grind)
    | (have r₁ := eq159212 X0
       have r₂ := eq31088 (k x y) (M.op x y) x
       grind)
    | (have r₁ := eq159212 X0
       have r₂ := eq31088 y x x
       grind)
    | exact resolve eq159212 eq31088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31088 eq159212
  have eq159301 : ∀ X0 : G, (τ (σ (k x x))) = X0 ∨ (M.op (σ x) (σ X0)) = (k (σ x) (σ X0)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq4210 (σ x) X0
       have i₂ := eq159224 x
       grind)
    | exact superpose eq159224 eq4210
    | (have j0 := eq4210 (σ x) X0
       have j1 := eq159224 x
       grind)
    | exact resolve eq4210 eq159224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4210 eq159224
  have eq159350 : ∀ X0 : G, (τ (σ (k x x))) = X0 ∨ (M.op (σ x) (σ X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq159301 X0
       have j1 := eq39513 (σ X0)
       grind)
    | (have r₁ := eq159301 X0
       have r₂ := eq39513 X0
       grind)
    | exact resolve eq159301 eq39513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39513 eq159301
  have eq159400 : ∀ X0 : G, (k x x) = X0 ∨ (M.op (σ x) (σ X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq159350 X0
       have i₂ := eq10 (k x x)
       grind)
    | exact superpose eq10 eq159350
    | (have j0 := eq159350 X0
       grind)
    | exact resolve eq159350 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159350
  have eq159429 : ∀ X0 : G, (M.op x x) = X0 ∨ (M.op (σ x) (σ X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq159400 X0
       have i₂ := eq83 x
       grind)
    | exact superpose eq83 eq159400
    | (have j0 := eq159400 X0
       grind)
    | exact resolve eq159400 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159400
  have eq159445 : ∀ X0 : G, y = X0 ∨ (M.op (σ x) (σ X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq159429 X0
       have i₂ := eq5827
       grind)
    | exact superpose eq5827 eq159429
    | (have j0 := eq159429 X0
       grind)
    | exact resolve eq159429 eq5827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159429
  have eq159454 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq159445 X0
       have i₂ := eq15 x X0
       grind)
    | exact superpose eq15 eq159445
    | (have j0 := eq159445 X0
       grind)
    | exact resolve eq159445 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159445
  have eq159612 : ∀ X0 : G, (τ (σ (k x x))) = X0 ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq339 (σ x) X0
       have i₂ := eq159454 x
       grind)
    | exact superpose eq159454 eq339
    | (have j0 := eq339 (σ x) X0
       have j1 := eq159454 x
       grind)
    | exact resolve eq339 eq159454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339 eq159454
  have eq159684 : ∀ X0 : G, (k x x) = X0 ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq159612 X0
       have i₂ := eq10 (k x x)
       grind)
    | exact superpose eq10 eq159612
    | (have j0 := eq159612 X0
       grind)
    | exact resolve eq159612 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159612
  have eq159745 : ∀ X0 : G, (M.op x x) = X0 ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq159684 X0
       have i₂ := eq83 x
       grind)
    | exact superpose eq83 eq159684
    | (have j0 := eq159684 X0
       grind)
    | exact resolve eq159684 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq159684
  have eq159774 : ∀ X0 : G, y = X0 ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq159745 X0
       have i₂ := eq5827
       grind)
    | exact superpose eq5827 eq159745
    | (have j0 := eq159745 X0
       grind)
    | exact resolve eq159745 eq5827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159745
  have eq159791 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ y = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq159774 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq159774
    | (have j0 := eq159774 X0
       grind)
    | exact resolve eq159774 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159774
  have eq159799 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq159791 X0
       have j1 := eq6255 X0
       grind)
    | (have r₁ := eq159791 x
       have r₂ := eq6255 X0
       grind)
    | (have r₁ := eq159791 X0
       have r₂ := eq6255 X0
       grind)
    | exact resolve eq159791 eq6255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6255 eq159791
  have eq159851 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq19 X0 x
       have i₂ := eq159799 (τ X0)
       grind)
    | exact superpose eq159799 eq19
    | (have j1 := eq159799 (τ X0)
       grind)
    | exact resolve eq19 eq159799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq159799
  have eq212116 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X2)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4134 X0 X1 X1
       have i₂ := eq311 X0 X1
       grind)
    | exact superpose eq311 eq4134
    | (have j0 := eq4134 X0 X1 X1
       have j1 := eq311 X0 X1
       grind)
    | exact resolve eq4134 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311 eq4134
  have eq213215 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X2)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq212116 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212116
  have eq213220 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq213215 X0 X1 x
       have j1 := eq88819 X0 X1 x
       grind)
    | (have r₁ := eq213215 X0 X1 x
       have r₂ := eq88819 X0 X1 x
       grind)
    | exact resolve eq213215 eq88819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88819 eq213215
  have eq213315 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op x (M.op x X0))) ∨ y = X0 ∨ (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq66194 X0
       have i₂ := eq213220 x (M.op x X0)
       grind)
    | exact superpose eq213220 eq66194
    | (have j0 := eq66194 X0
       have j1 := eq213220 x (M.op x X0)
       grind)
    | exact resolve eq66194 eq213220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66194 eq213220
  have eq213611 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = X0 ∨ (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq213315 X0
       have i₂ := eq6264 X0
       grind)
    | exact superpose eq6264 eq213315
    | (have j0 := eq213315 X0
       grind)
    | exact resolve eq213315 eq6264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213315
  have eq213686 : ∀ X0 : G, y = X0 ∨ (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq213611 X0
       grind)
    | (have r₁ := eq213611 X0
       have r₂ := eq16
       grind)
    | exact resolve eq213611 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213611
  have eq213706 : ∀ X0 : G, y = (M.op x X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq213686 X0
       have i₂ := eq5827
       grind)
    | exact superpose eq5827 eq213686
    | (have j0 := eq213686 (M.op x X0)
       grind)
    | exact resolve eq213686 eq5827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5827 eq213686
  have eq214702 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq6264 X0
       have i₂ := eq213706 (M.op x X0)
       grind)
    | exact superpose eq213706 eq6264
    | (have j1 := eq213706 y
       grind)
    | exact resolve eq6264 eq213706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6264
  have eq214708 : ∀ X0 : G, (σ y) = (k (σ x) X0) ∨ (τ X0) = y ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq159851 X0
       have i₂ := eq213706 (τ X0)
       grind)
    | exact superpose eq213706 eq159851
    | (have j0 := eq159851 X0
       have j1 := eq213706 (τ X0)
       grind)
    | exact resolve eq159851 eq213706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159851 eq213706
  have eq214838 : ∀ X0 : G, (σ y) = (k (σ x) X0) ∨ (τ X0) = y := by
    intro X0
    first
    | (have j0 := eq214708 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214708
  have eq216458 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq214702 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214702
  have eq216459 : y = (M.op x y) := by grind
  clear eq216458
  have eq218698 : ∀ X0 : G, (k (τ (σ x)) X0) = (τ (σ y)) ∨ (τ (σ X0)) = y := by
    intro X0
    first
    | (have i₁ := eq23 (σ x) X0
       have i₂ := eq214838 (σ X0)
       grind)
    | exact superpose eq214838 eq23
    | (have j1 := eq214838 (σ X0)
       grind)
    | exact resolve eq23 eq214838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq214838
  have eq218743 : ∀ X0 : G, y = (k (τ (σ x)) X0) ∨ (τ (σ X0)) = y := by
    intro X0
    first
    | (have i₁ := eq218698 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq218698
    | (have j0 := eq218698 X0
       grind)
    | exact resolve eq218698 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218698
  have eq218799 : ∀ X0 : G, y = (k x X0) ∨ (τ (σ X0)) = y := by
    intro X0
    first
    | (have i₁ := eq218743 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq218743
    | (have j0 := eq218743 X0
       grind)
    | exact resolve eq218743 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218743
  have eq218815 : ∀ X0 : G, y = (k x X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq218799 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq218799
    | (have j0 := eq218799 X0
       grind)
    | exact resolve eq218799 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218799
  have eq220129 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq33649
       have i₂ := eq218815 (τ (M.op (σ x) (σ y)))
       grind)
    | exact superpose eq218815 eq33649
    | (have j1 := eq218815 (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq33649 eq218815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33649 eq218815
  have eq220253 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq220129
  have eq223058 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq220253
       grind)
    | exact superpose eq220253 eq11
    | exact resolve eq11 eq220253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220253
  have eq226512 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq223058
       grind)
    | exact superpose eq223058 eq16
    | exact resolve eq16 eq223058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223058
  have eq226636 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq226512
       have i₂ := eq216459
       grind)
    | exact superpose eq216459 eq226512
    | exact resolve eq226512 eq216459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216459 eq226512
  have eq226637 : False := by grind
  exact eq226637

/-- `Equation4282`: `x ◇ (x ◇ y) = x ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_y_pxx_pxx_pxy_Equation4282 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4282 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4282.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = X1 := by
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
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq42 (σ X0)
       grind)
    | exact superpose eq42 eq15
    | exact resolve eq15 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq42 (τ X0)
       grind)
    | exact superpose eq42 eq19
    | exact resolve eq19 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq46
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq49 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq44 X0
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq44
    | exact resolve eq44 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq47
    | exact resolve eq47 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq47
  have eq55 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq73 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq86 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 X1
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq69
    | (have j0 := eq69 X0 X1
       grind)
    | exact resolve eq69 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq114 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 X2) ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X2)) ∨ (M.op X0 X2) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X1 X2
       grind)
    | (have i₁ := eq81 X0 (M.op X0 X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq81
    | (have j0 := eq81 X0 (M.op X0 X2)
       grind)
    | (have r₁ := eq81 X0 (M.op X0 (M.op X0 X2))
       have r₂ := eq9 X0 (M.op X0 X2) X2
       grind)
    | (have r₁ := eq81 X0 (M.op X0 (M.op X0 X1))
       have r₂ := eq9 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq81 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq125 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq9
    | exact resolve eq9 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq128 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq12
    | exact resolve eq12 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq127 X0
       have j1 := eq128 X0 (σ (M.op X0 X0))
       grind)
    | (have r₁ := eq127 X0
       have r₂ := eq128 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq127 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq128
  have eq133 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq130 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq130
    | exact resolve eq130 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq161 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq83
    | (have j0 := eq83 (σ X0) (σ (k X0 X1))
       grind)
    | exact resolve eq83 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq188 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq185 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq185 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq185 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq185 X0 X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq185 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq199 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq161 X0 X1
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq161
    | (have j0 := eq161 X0 X1
       grind)
    | exact resolve eq161 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq204 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 X1
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq199
    | (have j0 := eq199 X0 X1
       grind)
    | exact resolve eq199 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq396 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq397 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq396 X0 X1
       have j1 := eq204 X0 X1
       grind)
    | (have r₁ := eq396 X0 X1
       have r₂ := eq204 X0 X1
       grind)
    | (have r₁ := eq396 X0 X1
       have r₂ := eq204 X0 (k X0 X1)
       grind)
    | exact resolve eq396 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq396
  have eq674 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq188 X0 (τ X1)
       grind)
    | exact superpose eq188 eq19
    | (have j1 := eq188 X0 (τ X1)
       grind)
    | exact resolve eq19 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1334 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X2)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X2 (σ X1)
       have i₂ := eq397 X0 X1
       grind)
    | exact superpose eq397 eq9
    | (have j1 := eq397 X0 X1
       grind)
    | exact resolve eq9 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1384 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq397 X1 X0
       grind)
    | (have i₁ := eq10 X1
       have i₂ := eq397 X0 X1
       grind)
    | exact superpose eq397 eq10
    | (have j1 := eq397 X1 X0
       grind)
    | exact resolve eq10 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1391 : ∀ X0 X1 X2 : G, (τ (k X1 (σ X0))) = (k (τ X1) (M.op X2 X2)) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X1 (M.op X2 X2)
       have i₂ := eq397 X2 X0
       grind)
    | (have i₁ := eq23 X0 X1
       have i₂ := eq397 X0 X1
       grind)
    | exact superpose eq397 eq23
    | (have j1 := eq397 X2 X0
       grind)
    | exact resolve eq23 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq1413 : ∀ X0 X1 X2 : G, (k (τ X1) X0) = (k (τ X1) (M.op X2 X2)) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1391 X0 X1 X2
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq1391
    | (have j0 := eq1391 X0 X1 X2
       grind)
    | exact resolve eq1391 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1391
  have eq1420 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1384 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1384
    | (have j0 := eq1384 X0 X1
       grind)
    | exact resolve eq1384 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384
  have eq3140 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1420 y x
       grind)
    | exact superpose eq1420 eq16
    | (have j1 := eq1420 y x
       grind)
    | exact resolve eq16 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3338 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3140
       have i₂ := eq188 x y
       grind)
    | exact superpose eq188 eq3140
    | (have j1 := eq188 x y
       grind)
    | exact resolve eq3140 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq3140
  have eq3345 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq3338
  have eq3346 : y = (M.op x x) := by grind
  clear eq3345
  have eq3398 : ∀ X0 : G, y ≠ (M.op x X0) ∨ y = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x x
       have i₂ := eq3346
       grind)
    | exact superpose eq3346 eq12
    | exact resolve eq12 eq3346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3400 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq125 x X0
       have i₂ := eq3346
       grind)
    | exact superpose eq3346 eq125
    | exact resolve eq125 eq3346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq3406 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 x
       have i₂ := eq3346
       grind)
    | exact superpose eq3346 eq9
    | exact resolve eq9 eq3346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4402 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 (M.op X0 X1)) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq4941 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k x X0))) ∨ (M.op x x) = X0 := by
    intro X0
    first
    | (have i₁ := eq3400 (σ X0)
       have i₂ := eq1420 X0 x
       grind)
    | exact superpose eq1420 eq3400
    | (have j1 := eq1420 X0 x
       grind)
    | exact resolve eq3400 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420
  have eq4997 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq4941 X0
       have i₂ := eq3346
       grind)
    | exact superpose eq3346 eq4941
    | (have j0 := eq4941 X0
       grind)
    | exact resolve eq4941 eq3346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4941
  have eq29605 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq674 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq674
    | exact resolve eq674 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq30042 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29605 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq29605
    | (have j0 := eq29605 X0 X1
       grind)
    | exact resolve eq29605 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29605
  have eq55712 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 ∨ (M.op x x) = X0 := by
    intro X0
    first
    | (have i₁ := eq4997 X0
       have i₂ := eq30042 X0 x
       grind)
    | exact superpose eq30042 eq4997
    | (have j0 := eq4997 X0
       have j1 := eq30042 X0 x
       grind)
    | exact resolve eq4997 eq30042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4997 eq30042
  have eq55909 : ∀ X0 : G, y = X0 ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq55712 X0
       have i₂ := eq3346
       grind)
    | exact superpose eq3346 eq55712
    | (have j0 := eq55712 X0
       grind)
    | exact resolve eq55712 eq3346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55712
  have eq55910 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq55909 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55909
  have eq57743 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (k (τ X0) X1)) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq133 (τ X0)
       have i₂ := eq1413 X1 X0 (τ X0)
       grind)
    | (have i₁ := eq133 (τ X1)
       have i₂ := eq1413 (M.op (τ X1) (τ X1)) X1 x
       grind)
    | exact superpose eq1413 eq133
    | (have j1 := eq1413 X1 X1 (τ X0)
       grind)
    | exact resolve eq133 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq1413
  have eq57940 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k (τ X0) X1)) ∨ (σ (k (τ X0) X1)) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq57743 X0 X1
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq57743
    | (have j0 := eq57743 X0 X1
       grind)
    | exact resolve eq57743 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57743
  have eq58098 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq57940 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq57940
    | (have j0 := eq57940 X0 X1
       grind)
    | exact resolve eq57940 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57940
  have eq58173 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq58098 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq58098
    | (have j0 := eq58098 X0 X1
       grind)
    | exact resolve eq58098 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58098
  have eq58227 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq58173 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq58173
    | (have j0 := eq58173 X0 X1
       grind)
    | exact resolve eq58173 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq58173
  have eq69121 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X1) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq58227 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq58227
    | exact resolve eq58227 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69505 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq58227 (σ X0) X1
       grind)
    | exact superpose eq58227 eq37
    | (have j1 := eq58227 (σ X0) X1
       grind)
    | exact resolve eq37 eq58227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58227
  have eq69580 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq69505 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq69505
    | (have j0 := eq69505 X0 X1
       grind)
    | exact resolve eq69505 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69505
  have eq69749 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq69580 X0 X1
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq69580
    | (have j0 := eq69580 X0 X1
       grind)
    | exact resolve eq69580 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69580
  have eq69833 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq69749 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq69749
    | (have j0 := eq69749 X0 X1
       grind)
    | exact resolve eq69749 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69749
  have eq69895 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq69833 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq69833
    | (have j0 := eq69833 X0 X1
       grind)
    | exact resolve eq69833 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69833
  have eq70267 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) (M.op (σ (τ X0)) X2)) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1334 (τ X0) (τ X1) X2
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq1334
    | (have j0 := eq1334 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq1334 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1334
  have eq70636 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) (M.op (σ (τ X0)) X2)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70267 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq70267
    | (have j0 := eq70267 X0 X1 X2
       grind)
    | exact resolve eq70267 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70267
  have eq70715 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) = (M.op X0 (k X0 X1)) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70636 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq70636
    | (have j0 := eq70636 X0 X1 X2
       grind)
    | exact resolve eq70636 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70636
  have eq70737 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X0 (M.op X0 X2)) = (M.op X0 (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70715 X0 X1 X2
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq70715
    | (have j0 := eq70715 X0 X1 X2
       grind)
    | exact resolve eq70715 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq70715
  have eq70744 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) = (M.op X0 (k X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70737 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq70737
    | (have j0 := eq70737 X0 X1 X2
       grind)
    | exact resolve eq70737 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70737
  have eq71381 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq69121 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72062 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 X0) ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71381 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X1 X2
       grind)
    | (have i₁ := eq71381 X0 (M.op X0 X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq71381
    | (have j0 := eq71381 X0 (M.op X0 X1)
       grind)
    | exact resolve eq71381 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72103 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq71381 (σ x) (M.op (σ x) X0)
       have i₂ := eq3400 X0
       grind)
    | exact superpose eq3400 eq71381
    | (have j0 := eq71381 (σ x) (σ y)
       grind)
    | exact resolve eq71381 eq3400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71381
  have eq72277 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq72103 X0
       have i₂ := eq49 x
       grind)
    | exact superpose eq49 eq72103
    | (have j0 := eq72103 X0
       grind)
    | exact resolve eq72103 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72103
  have eq72314 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq72277 X0
       have i₂ := eq3346
       grind)
    | exact superpose eq3346 eq72277
    | (have j0 := eq72277 X0
       grind)
    | exact resolve eq72277 eq3346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72277
  have eq72451 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 (M.op X0 X1)) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4402 X0 X1
       have i₂ := eq9 X0 X1 x
       grind)
    | (have i₁ := eq4402 X0 x
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq4402
    | (have j0 := eq4402 X0 X1
       grind)
    | exact resolve eq4402 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72486 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4402 (σ x) x
       have i₂ := eq3400 x
       grind)
    | exact superpose eq3400 eq4402
    | exact resolve eq4402 eq3400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3400 eq4402
  have eq72762 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq72486
       have i₂ := eq49 x
       grind)
    | exact superpose eq49 eq72486
    | exact resolve eq72486 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq72486
  have eq72773 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq72451 X0 X1
       have j1 := eq72062 X0 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq72451 X0 X1
       have r₂ := eq72062 X0 X1 x
       grind)
    | exact resolve eq72451 eq72062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72062 eq72451
  have eq72855 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq72762
       have i₂ := eq3346
       grind)
    | exact superpose eq3346 eq72762
    | exact resolve eq72762 eq3346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72762
  have eq72867 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have j1 := eq72314 (σ y)
       grind)
    | (have r₁ := eq72855
       have r₂ := eq72314 x
       grind)
    | exact resolve eq72855 eq72314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72314 eq72855
  have eq77261 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq37 x (M.op (σ x) (σ y))
       have i₂ := eq72867
       grind)
    | exact superpose eq72867 eq37
    | exact resolve eq37 eq72867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq72867
  have eq81818 : ∀ X0 X1 : G, y ≠ (M.op x (M.op x X0)) ∨ y = (k x (k x X1)) ∨ (M.op x x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3398 (k x X1)
       have i₂ := eq70744 x X1 X0
       grind)
    | exact superpose eq70744 eq3398
    | (have j0 := eq3398 (M.op x X0)
       have j1 := eq70744 x X1 x
       grind)
    | (have r₁ := eq3398 x
       have r₂ := eq70744 x y x
       grind)
    | exact resolve eq3398 eq70744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3398 eq70744
  have eq81841 : ∀ X1 : G, y ≠ (M.op x y) ∨ y = (k x (k x X1)) ∨ (M.op x x) = X1 := by
    intro X1
    first
    | (have i₁ := eq81818 x X1
       have i₂ := eq3406 x
       grind)
    | exact superpose eq3406 eq81818
    | (have j0 := eq81818 x X1
       grind)
    | exact resolve eq81818 eq3406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81818
  have eq81936 : ∀ X1 : G, y ≠ (M.op x y) ∨ y = X1 ∨ y = (k x (k x X1)) := by
    intro X1
    first
    | (have i₁ := eq81841 X1
       have i₂ := eq3346
       grind)
    | exact superpose eq3346 eq81841
    | (have j0 := eq81841 X1
       grind)
    | exact resolve eq81841 eq3346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81841
  have eq131054 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq69895 X1 X0
       have i₂ := eq69121 X0 X1
       grind)
    | exact superpose eq69121 eq69895
    | (have j0 := eq69895 X0 X1
       have j1 := eq69121 X1 X0
       grind)
    | exact resolve eq69895 eq69121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69121 eq69895
  have eq132104 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq131054 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq131054 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq131054 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq131054 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131054
  have eq191251 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op x (M.op x X0))) ∨ y = X0 ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq55910 X0
       have i₂ := eq132104 x (M.op x X0)
       grind)
    | exact superpose eq132104 eq55910
    | (have j0 := eq55910 X0
       have j1 := eq132104 x (M.op x X0)
       grind)
    | exact resolve eq55910 eq132104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55910 eq132104
  have eq191461 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = X0 ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq191251 X0
       have i₂ := eq3406 X0
       grind)
    | exact superpose eq3406 eq191251
    | (have j0 := eq191251 X0
       grind)
    | exact resolve eq191251 eq3406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191251
  have eq191501 : ∀ X0 : G, y = X0 ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq191461 X0
       grind)
    | (have r₁ := eq191461 X0
       have r₂ := eq16
       grind)
    | exact resolve eq191461 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191461
  have eq191512 : ∀ X0 : G, y = (k x (M.op x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq191501 X0
       have i₂ := eq3346
       grind)
    | exact superpose eq3346 eq191501
    | (have j0 := eq191501 (k x (M.op x X0))
       grind)
    | exact resolve eq191501 eq3346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3346 eq191501
  have eq193087 : ∀ X0 : G, y = (M.op x (M.op x X0)) ∨ y = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq72773 x X0
       have i₂ := eq191512 (M.op x X0)
       grind)
    | exact superpose eq191512 eq72773
    | (have j1 := eq191512 (M.op x (M.op x X0))
       grind)
    | exact resolve eq72773 eq191512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72773 eq191512
  have eq193158 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq193087 X0
       have i₂ := eq3406 X0
       grind)
    | exact superpose eq3406 eq193087
    | (have j0 := eq193087 y
       grind)
    | exact resolve eq193087 eq3406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3406 eq193087
  have eq193756 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq193158 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193158
  have eq193757 : y = (M.op x y) := by grind
  clear eq193756
  have eq194903 : ∀ X0 : G, y ≠ y ∨ y = X0 ∨ y = (k x (k x X0)) := by
    intro X0
    first
    | (have i₁ := eq81936 X0
       have i₂ := eq193757
       grind)
    | exact superpose eq193757 eq81936
    | (have j0 := eq81936 X0
       grind)
    | (have r₁ := eq81936 x
       have r₂ := eq193757
       grind)
    | exact resolve eq81936 eq193757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81936
  have eq194942 : ∀ X0 : G, y = (k x (k x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq194903 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194903
  have eq200369 : y = (k x (τ (M.op (σ x) (σ y)))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq194942 (τ (M.op (σ x) (σ y)))
       have i₂ := eq77261
       grind)
    | exact superpose eq77261 eq194942
    | (have j0 := eq194942 (k x (τ (M.op (σ x) (σ y))))
       grind)
    | exact resolve eq194942 eq77261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194942
  have eq200542 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq200369
       have i₂ := eq77261
       grind)
    | exact superpose eq77261 eq200369
    | exact resolve eq200369 eq77261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77261 eq200369
  have eq200543 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq200542
  have eq201783 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq200543
       grind)
    | exact superpose eq200543 eq11
    | exact resolve eq11 eq200543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200543
  have eq204413 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq201783
       grind)
    | exact superpose eq201783 eq16
    | exact resolve eq16 eq201783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201783
  have eq204525 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq204413
       have i₂ := eq193757
       grind)
    | exact superpose eq193757 eq204413
    | exact resolve eq204413 eq193757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193757 eq204413
  have eq204526 : False := by grind
  exact eq204526

/-- `Equation4282`: `x ◇ (x ◇ y) = x ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_y_pxx_y_pxy_Equation4282 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4282 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4282.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = X1 := by
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
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq42 (σ X0)
       grind)
    | exact superpose eq42 eq15
    | exact resolve eq15 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq42 (τ X0)
       grind)
    | exact superpose eq42 eq19
    | exact resolve eq19 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq46
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq49 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq44 X0
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq44
    | exact resolve eq44 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq47
    | exact resolve eq47 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq47
  have eq55 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq73 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq86 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 X1
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq69
    | (have j0 := eq69 X0 X1
       grind)
    | exact resolve eq69 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq114 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 X2) ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X2)) ∨ (M.op X0 X2) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X1 X2
       grind)
    | (have i₁ := eq81 X0 (M.op X0 X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq81
    | (have j0 := eq81 X0 (M.op X0 X2)
       grind)
    | (have r₁ := eq81 X0 (M.op X0 (M.op X0 X2))
       have r₂ := eq9 X0 (M.op X0 X2) X2
       grind)
    | (have r₁ := eq81 X0 (M.op X0 (M.op X0 X1))
       have r₂ := eq9 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq81 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq125 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq9
    | exact resolve eq9 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq128 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq12
    | exact resolve eq12 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq127 X0
       have j1 := eq128 X0 (σ (M.op X0 X0))
       grind)
    | (have r₁ := eq127 X0
       have r₂ := eq128 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq127 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq128
  have eq133 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq130 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq130
    | exact resolve eq130 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq161 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq83
    | (have j0 := eq83 (σ X0) (σ (k X0 X1))
       grind)
    | exact resolve eq83 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq188 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq185 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq185 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq185 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq185 X0 X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq185 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq199 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq161 X0 X1
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq161
    | (have j0 := eq161 X0 X1
       grind)
    | exact resolve eq161 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq204 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 X1
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq199
    | (have j0 := eq199 X0 X1
       grind)
    | exact resolve eq199 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq396 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq397 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq396 X0 X1
       have j1 := eq204 X0 X1
       grind)
    | (have r₁ := eq396 X0 X1
       have r₂ := eq204 X0 X1
       grind)
    | (have r₁ := eq396 X0 X1
       have r₂ := eq204 X0 (k X0 X1)
       grind)
    | exact resolve eq396 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq396
  have eq674 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq188 X0 (τ X1)
       grind)
    | exact superpose eq188 eq19
    | (have j1 := eq188 X0 (τ X1)
       grind)
    | exact resolve eq19 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1334 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X2)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X2 (σ X1)
       have i₂ := eq397 X0 X1
       grind)
    | exact superpose eq397 eq9
    | (have j1 := eq397 X0 X1
       grind)
    | exact resolve eq9 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1384 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq397 X1 X0
       grind)
    | (have i₁ := eq10 X1
       have i₂ := eq397 X0 X1
       grind)
    | exact superpose eq397 eq10
    | (have j1 := eq397 X1 X0
       grind)
    | exact resolve eq10 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1391 : ∀ X0 X1 X2 : G, (τ (k X1 (σ X0))) = (k (τ X1) (M.op X2 X2)) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X1 (M.op X2 X2)
       have i₂ := eq397 X2 X0
       grind)
    | (have i₁ := eq23 X0 X1
       have i₂ := eq397 X0 X1
       grind)
    | exact superpose eq397 eq23
    | (have j1 := eq397 X2 X0
       grind)
    | exact resolve eq23 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq1413 : ∀ X0 X1 X2 : G, (k (τ X1) X0) = (k (τ X1) (M.op X2 X2)) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1391 X0 X1 X2
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq1391
    | (have j0 := eq1391 X0 X1 X2
       grind)
    | exact resolve eq1391 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1391
  have eq1420 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1384 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1384
    | (have j0 := eq1384 X0 X1
       grind)
    | exact resolve eq1384 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384
  have eq3140 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1420 y x
       grind)
    | exact superpose eq1420 eq16
    | (have j1 := eq1420 y x
       grind)
    | exact resolve eq16 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3338 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3140
       have i₂ := eq188 x y
       grind)
    | exact superpose eq188 eq3140
    | (have j1 := eq188 x y
       grind)
    | exact resolve eq3140 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq3140
  have eq3345 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq3338
  have eq3346 : y = (M.op x x) := by grind
  clear eq3345
  have eq3398 : ∀ X0 : G, y ≠ (M.op x X0) ∨ y = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x x
       have i₂ := eq3346
       grind)
    | exact superpose eq3346 eq12
    | exact resolve eq12 eq3346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3400 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq125 x X0
       have i₂ := eq3346
       grind)
    | exact superpose eq3346 eq125
    | exact resolve eq125 eq3346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq3406 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 x
       have i₂ := eq3346
       grind)
    | exact superpose eq3346 eq9
    | exact resolve eq9 eq3346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4402 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 (M.op X0 X1)) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq4941 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k x X0))) ∨ (M.op x x) = X0 := by
    intro X0
    first
    | (have i₁ := eq3400 (σ X0)
       have i₂ := eq1420 X0 x
       grind)
    | exact superpose eq1420 eq3400
    | (have j1 := eq1420 X0 x
       grind)
    | exact resolve eq3400 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420
  have eq4997 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq4941 X0
       have i₂ := eq3346
       grind)
    | exact superpose eq3346 eq4941
    | (have j0 := eq4941 X0
       grind)
    | exact resolve eq4941 eq3346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4941
  have eq29605 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq674 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq674
    | exact resolve eq674 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq30042 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29605 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq29605
    | (have j0 := eq29605 X0 X1
       grind)
    | exact resolve eq29605 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29605
  have eq55712 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 ∨ (M.op x x) = X0 := by
    intro X0
    first
    | (have i₁ := eq4997 X0
       have i₂ := eq30042 X0 x
       grind)
    | exact superpose eq30042 eq4997
    | (have j0 := eq4997 X0
       have j1 := eq30042 X0 x
       grind)
    | exact resolve eq4997 eq30042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4997 eq30042
  have eq55909 : ∀ X0 : G, y = X0 ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq55712 X0
       have i₂ := eq3346
       grind)
    | exact superpose eq3346 eq55712
    | (have j0 := eq55712 X0
       grind)
    | exact resolve eq55712 eq3346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55712
  have eq55910 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq55909 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55909
  have eq57743 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (k (τ X0) X1)) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq133 (τ X0)
       have i₂ := eq1413 X1 X0 (τ X0)
       grind)
    | (have i₁ := eq133 (τ X1)
       have i₂ := eq1413 (M.op (τ X1) (τ X1)) X1 x
       grind)
    | exact superpose eq1413 eq133
    | (have j1 := eq1413 X1 X1 (τ X0)
       grind)
    | exact resolve eq133 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq1413
  have eq57940 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k (τ X0) X1)) ∨ (σ (k (τ X0) X1)) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq57743 X0 X1
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq57743
    | (have j0 := eq57743 X0 X1
       grind)
    | exact resolve eq57743 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57743
  have eq58098 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq57940 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq57940
    | (have j0 := eq57940 X0 X1
       grind)
    | exact resolve eq57940 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57940
  have eq58173 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq58098 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq58098
    | (have j0 := eq58098 X0 X1
       grind)
    | exact resolve eq58098 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58098
  have eq58227 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq58173 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq58173
    | (have j0 := eq58173 X0 X1
       grind)
    | exact resolve eq58173 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq58173
  have eq69121 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X1) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq58227 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq58227
    | exact resolve eq58227 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69505 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq58227 (σ X0) X1
       grind)
    | exact superpose eq58227 eq37
    | (have j1 := eq58227 (σ X0) X1
       grind)
    | exact resolve eq37 eq58227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58227
  have eq69580 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq69505 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq69505
    | (have j0 := eq69505 X0 X1
       grind)
    | exact resolve eq69505 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69505
  have eq69749 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq69580 X0 X1
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq69580
    | (have j0 := eq69580 X0 X1
       grind)
    | exact resolve eq69580 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69580
  have eq69833 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq69749 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq69749
    | (have j0 := eq69749 X0 X1
       grind)
    | exact resolve eq69749 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69749
  have eq69895 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq69833 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq69833
    | (have j0 := eq69833 X0 X1
       grind)
    | exact resolve eq69833 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69833
  have eq70267 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) (M.op (σ (τ X0)) X2)) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1334 (τ X0) (τ X1) X2
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq1334
    | (have j0 := eq1334 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq1334 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1334
  have eq70636 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) (M.op (σ (τ X0)) X2)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70267 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq70267
    | (have j0 := eq70267 X0 X1 X2
       grind)
    | exact resolve eq70267 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70267
  have eq70715 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) = (M.op X0 (k X0 X1)) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70636 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq70636
    | (have j0 := eq70636 X0 X1 X2
       grind)
    | exact resolve eq70636 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70636
  have eq70737 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X0 (M.op X0 X2)) = (M.op X0 (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70715 X0 X1 X2
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq70715
    | (have j0 := eq70715 X0 X1 X2
       grind)
    | exact resolve eq70715 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq70715
  have eq70744 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) = (M.op X0 (k X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70737 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq70737
    | (have j0 := eq70737 X0 X1 X2
       grind)
    | exact resolve eq70737 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70737
  have eq71381 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq69121 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72062 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 X0) ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71381 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X1 X2
       grind)
    | (have i₁ := eq71381 X0 (M.op X0 X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq71381
    | (have j0 := eq71381 X0 (M.op X0 X1)
       grind)
    | exact resolve eq71381 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72103 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq71381 (σ x) (M.op (σ x) X0)
       have i₂ := eq3400 X0
       grind)
    | exact superpose eq3400 eq71381
    | (have j0 := eq71381 (σ x) (σ y)
       grind)
    | exact resolve eq71381 eq3400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71381
  have eq72277 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq72103 X0
       have i₂ := eq49 x
       grind)
    | exact superpose eq49 eq72103
    | (have j0 := eq72103 X0
       grind)
    | exact resolve eq72103 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72103
  have eq72314 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq72277 X0
       have i₂ := eq3346
       grind)
    | exact superpose eq3346 eq72277
    | (have j0 := eq72277 X0
       grind)
    | exact resolve eq72277 eq3346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72277
  have eq72451 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 (M.op X0 X1)) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4402 X0 X1
       have i₂ := eq9 X0 X1 x
       grind)
    | (have i₁ := eq4402 X0 x
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq4402
    | (have j0 := eq4402 X0 X1
       grind)
    | exact resolve eq4402 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72486 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4402 (σ x) x
       have i₂ := eq3400 x
       grind)
    | exact superpose eq3400 eq4402
    | exact resolve eq4402 eq3400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3400 eq4402
  have eq72762 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq72486
       have i₂ := eq49 x
       grind)
    | exact superpose eq49 eq72486
    | exact resolve eq72486 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq72486
  have eq72773 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq72451 X0 X1
       have j1 := eq72062 X0 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq72451 X0 X1
       have r₂ := eq72062 X0 X1 x
       grind)
    | exact resolve eq72451 eq72062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72062 eq72451
  have eq72855 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq72762
       have i₂ := eq3346
       grind)
    | exact superpose eq3346 eq72762
    | exact resolve eq72762 eq3346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72762
  have eq72867 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have j1 := eq72314 (σ y)
       grind)
    | (have r₁ := eq72855
       have r₂ := eq72314 x
       grind)
    | exact resolve eq72855 eq72314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72314 eq72855
  have eq77261 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq37 x (M.op (σ x) (σ y))
       have i₂ := eq72867
       grind)
    | exact superpose eq72867 eq37
    | exact resolve eq37 eq72867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq72867
  have eq81818 : ∀ X0 X1 : G, y ≠ (M.op x (M.op x X0)) ∨ y = (k x (k x X1)) ∨ (M.op x x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3398 (k x X1)
       have i₂ := eq70744 x X1 X0
       grind)
    | exact superpose eq70744 eq3398
    | (have j0 := eq3398 (M.op x X0)
       have j1 := eq70744 x X1 x
       grind)
    | (have r₁ := eq3398 x
       have r₂ := eq70744 x y x
       grind)
    | exact resolve eq3398 eq70744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3398 eq70744
  have eq81841 : ∀ X1 : G, y ≠ (M.op x y) ∨ y = (k x (k x X1)) ∨ (M.op x x) = X1 := by
    intro X1
    first
    | (have i₁ := eq81818 x X1
       have i₂ := eq3406 x
       grind)
    | exact superpose eq3406 eq81818
    | (have j0 := eq81818 x X1
       grind)
    | exact resolve eq81818 eq3406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81818
  have eq81936 : ∀ X1 : G, y ≠ (M.op x y) ∨ y = X1 ∨ y = (k x (k x X1)) := by
    intro X1
    first
    | (have i₁ := eq81841 X1
       have i₂ := eq3346
       grind)
    | exact superpose eq3346 eq81841
    | (have j0 := eq81841 X1
       grind)
    | exact resolve eq81841 eq3346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81841
  have eq131054 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq69895 X1 X0
       have i₂ := eq69121 X0 X1
       grind)
    | exact superpose eq69121 eq69895
    | (have j0 := eq69895 X0 X1
       have j1 := eq69121 X1 X0
       grind)
    | exact resolve eq69895 eq69121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69121 eq69895
  have eq132104 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq131054 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq131054 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq131054 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq131054 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131054
  have eq197338 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op x (M.op x X0))) ∨ y = X0 ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq55910 X0
       have i₂ := eq132104 x (M.op x X0)
       grind)
    | exact superpose eq132104 eq55910
    | (have j0 := eq55910 X0
       have j1 := eq132104 x (M.op x X0)
       grind)
    | exact resolve eq55910 eq132104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55910 eq132104
  have eq197548 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = X0 ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq197338 X0
       have i₂ := eq3406 X0
       grind)
    | exact superpose eq3406 eq197338
    | (have j0 := eq197338 X0
       grind)
    | exact resolve eq197338 eq3406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197338
  have eq197588 : ∀ X0 : G, y = X0 ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq197548 X0
       grind)
    | (have r₁ := eq197548 X0
       have r₂ := eq16
       grind)
    | exact resolve eq197548 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197548
  have eq197599 : ∀ X0 : G, y = (k x (M.op x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq197588 X0
       have i₂ := eq3346
       grind)
    | exact superpose eq3346 eq197588
    | (have j0 := eq197588 (k x (M.op x X0))
       grind)
    | exact resolve eq197588 eq3346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3346 eq197588
  have eq198091 : ∀ X0 : G, y = (M.op x (M.op x X0)) ∨ y = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq72773 x X0
       have i₂ := eq197599 (M.op x X0)
       grind)
    | exact superpose eq197599 eq72773
    | (have j1 := eq197599 (M.op x (M.op x X0))
       grind)
    | exact resolve eq72773 eq197599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72773 eq197599
  have eq198162 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq198091 X0
       have i₂ := eq3406 X0
       grind)
    | exact superpose eq3406 eq198091
    | (have j0 := eq198091 y
       grind)
    | exact resolve eq198091 eq3406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3406 eq198091
  have eq199438 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq198162 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198162
  have eq199439 : y = (M.op x y) := by grind
  clear eq199438
  have eq199704 : ∀ X0 : G, y ≠ y ∨ y = X0 ∨ y = (k x (k x X0)) := by
    intro X0
    first
    | (have i₁ := eq81936 X0
       have i₂ := eq199439
       grind)
    | exact superpose eq199439 eq81936
    | (have j0 := eq81936 X0
       grind)
    | (have r₁ := eq81936 x
       have r₂ := eq199439
       grind)
    | exact resolve eq81936 eq199439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81936
  have eq199743 : ∀ X0 : G, y = (k x (k x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq199704 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199704
  have eq206103 : y = (k x (τ (M.op (σ x) (σ y)))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq199743 (τ (M.op (σ x) (σ y)))
       have i₂ := eq77261
       grind)
    | exact superpose eq77261 eq199743
    | (have j0 := eq199743 (k x (τ (M.op (σ x) (σ y))))
       grind)
    | exact resolve eq199743 eq77261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199743
  have eq206277 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq206103
       have i₂ := eq77261
       grind)
    | exact superpose eq77261 eq206103
    | exact resolve eq206103 eq77261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77261 eq206103
  have eq206278 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq206277
  have eq207481 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq206278
       grind)
    | exact superpose eq206278 eq11
    | exact resolve eq11 eq206278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206278
  have eq210110 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq207481
       grind)
    | exact superpose eq207481 eq16
    | exact resolve eq16 eq207481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207481
  have eq210222 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq210110
       have i₂ := eq199439
       grind)
    | exact superpose eq199439 eq210110
    | exact resolve eq210110 eq199439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199439 eq210110
  have eq210223 : False := by grind
  exact eq210223

/-- `Equation4282`: `x ◇ (x ◇ y) = x ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pxy_pxx_pxy_Equation4282 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4282 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4282.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq40 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq63 : ∀ X0 X1 X2 : G, X0 = X2 ∨ X0 = X1 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq14 X0 X1
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | (have j0 := eq14 X1 X1
       have j1 := eq14 X1 X1
       grind)
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X1 X2)) ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq78 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq67 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq80 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq78 (M.op X0 X1) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq78 (k X0 X1) (M.op X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq78 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq78 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq82 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq70 (M.op X0 X0) X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq70 X0 (M.op X0 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq70 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq70 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq83 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X1 X2)) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq69 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq69 X0 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq69 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq85 : ∀ X0 X1 X2 : G, X0 = X2 ∨ X0 = X1 ∨ (M.op X1 X2) = (k X1 X2) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq63 X0 X1 X2
       have j1 := eq12 X1 X2
       grind)
    | (have r₁ := eq63 (M.op X0 X0) X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq63 X0 X1 (M.op X0 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq63 (M.op X0 X0) X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq63 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq87 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       have j1 := eq80 X1 X0
       grind)
    | (have r₁ := eq82 X1 X1
       have r₂ := eq80 (k X1 X1) X1
       grind)
    | (have r₁ := eq82 X0 X1
       have r₂ := eq80 X0 (k X1 X0)
       grind)
    | (have r₁ := eq82 X0 X1
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq82 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq88 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq85 X0 X1 X2
       have j1 := eq80 X1 X2
       grind)
    | (have r₁ := eq85 X0 X1 X1
       have r₂ := eq80 X0 X1
       grind)
    | (have r₁ := eq85 X1 X1 X0
       have r₂ := eq80 X0 X1
       grind)
    | (have r₁ := eq85 X0 X1 X2
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq85 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq90 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq80 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq98 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq87 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq101 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq90 (σ X0)
       grind)
    | exact superpose eq90 eq15
    | exact resolve eq15 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq90 (τ X0)
       grind)
    | exact superpose eq90 eq19
    | exact resolve eq19 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq105 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq105
    | exact resolve eq105 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq110 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq101 X0
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq101
    | exact resolve eq101 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq112 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq106 X0
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq106
    | exact resolve eq106 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq121 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq98 X0 (M.op X0 X2)
       have i₂ := eq9 X0 X2 X1
       grind)
    | (have i₁ := eq98 X0 (M.op X0 X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq98
    | (have j0 := eq98 X0 (M.op X0 X2)
       grind)
    | (have r₁ := eq98 X0 (M.op X0 (M.op X0 X2))
       have r₂ := eq9 X0 (M.op X0 X2) X2
       grind)
    | (have r₁ := eq98 X0 (M.op X0 (M.op X0 X1))
       have r₂ := eq9 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq98 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq153 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (M.op (σ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq83 (σ X1) (σ X0) X2
       grind)
    | exact superpose eq83 eq15
    | (have j1 := eq83 (σ X1) (σ X0) X2
       grind)
    | exact resolve eq15 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq90 (τ X0)
       have i₂ := eq40 X0 X0
       grind)
    | exact superpose eq40 eq90
    | exact resolve eq90 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq175 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq171 X0
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq171
    | exact resolve eq171 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq193 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = X2 ∨ (M.op (σ X0) X2) = (k (σ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq88 (σ X1) (σ X0) X2
       grind)
    | exact superpose eq88 eq15
    | (have j1 := eq88 (σ X1) (σ X0) X2
       grind)
    | exact resolve eq15 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq210 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq9
    | exact resolve eq9 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq256 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq255 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq357 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) X1
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq14
    | (have j0 := eq14 (τ X0) X1
       grind)
    | exact resolve eq14 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq12
    | (have j0 := eq12 (τ X0) X1
       grind)
    | exact resolve eq12 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq357 X0 X1
       have j1 := eq359 X0 X1
       grind)
    | (have r₁ := eq357 X0 X1
       have r₂ := eq359 X0 X1
       grind)
    | (have r₁ := eq357 X0 (τ (M.op (M.op X0 X0) (M.op X0 X0)))
       have r₂ := eq359 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq357 X0 (τ X0)
       have r₂ := eq359 X0 X1
       grind)
    | exact resolve eq357 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq359
  have eq435 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq72 X0 X1
       grind)
    | exact superpose eq72 eq10
    | (have j1 := eq72 X0 X1
       grind)
    | exact resolve eq10 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq502 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq435 X0 X1
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq435
    | (have j0 := eq435 X0 X1
       grind)
    | exact resolve eq435 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq564 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq502 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq502
    | (have j0 := eq502 X0 X1
       grind)
    | exact resolve eq502 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq615 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq564 X0 X1
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq564
    | (have j0 := eq564 X0 X1
       grind)
    | exact resolve eq564 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq656 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq256 (σ X0) (σ X1)
       grind)
    | exact superpose eq256 eq15
    | (have j1 := eq256 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq256 X0 (τ X1)
       grind)
    | exact superpose eq256 eq19
    | (have j1 := eq256 X0 (τ X1)
       grind)
    | exact resolve eq19 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq685 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq656 X0 X1
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq656
    | (have j0 := eq656 X0 X1
       grind)
    | exact resolve eq656 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq3775 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq615 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq615
    | (have j0 := eq615 (τ X0) X1
       grind)
    | exact resolve eq615 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3811 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (σ (k X0 X2)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X2 ∨ (M.op (σ X0) (σ X2)) = (k (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq615 X0 X2
       have i₂ := eq83 (σ X2) (σ X0) X1
       grind)
    | exact superpose eq83 eq615
    | (have j0 := eq615 X0 X2
       have j1 := eq83 (σ X2) (σ X0) X2
       grind)
    | exact resolve eq615 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq615
  have eq3999 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (σ (k X0 X2)) ∨ (M.op X0 X0) = X2 ∨ (M.op (σ X0) (σ X2)) = (k (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3811 X0 X1 X2
       have j1 := eq214 X0 (σ X2)
       grind)
    | (have r₁ := eq3811 X0 X1 X2
       have r₂ := eq214 X0 X1
       grind)
    | exact resolve eq3811 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3811
  have eq4018 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3775 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq3775
    | (have j0 := eq3775 X0 X1
       grind)
    | exact resolve eq3775 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3775
  have eq4075 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (σ (k X0 X2)) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (M.op X0 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3999 X0 X1 X2
       have i₂ := eq15 X0 X2
       grind)
    | exact superpose eq15 eq3999
    | (have j0 := eq3999 X0 X1 X2
       grind)
    | exact resolve eq3999 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3999
  have eq4087 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4018 X0 X1
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq4018
    | (have j0 := eq4018 X0 X1
       grind)
    | exact resolve eq4018 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq4018
  have eq4125 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4087 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq4087 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq4087 X0 (τ X0)
       have r₂ := eq12 (τ X0) X1
       grind)
    | (have r₁ := eq4087 X0 (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))
       have r₂ := eq12 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact resolve eq4087 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4087
  have eq4151 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4125 X0 X1
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq4125
    | (have j0 := eq4125 X0 X1
       grind)
    | exact resolve eq4125 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq4125
  have eq4271 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq4151 (σ X0) X1
       grind)
    | exact superpose eq4151 eq15
    | (have j1 := eq4151 (σ X0) X1
       grind)
    | exact resolve eq15 eq4151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4293 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4271 X0 X1
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq4271
    | (have j0 := eq4271 X0 X1
       grind)
    | exact resolve eq4271 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq4271
  have eq4314 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4293 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq4293
    | (have j0 := eq4293 X0 X1
       grind)
    | exact resolve eq4293 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4293
  have eq5073 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (M.op (σ X0) X2)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq153 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq5224 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4314 x y
       grind)
    | exact superpose eq4314 eq16
    | (have j1 := eq4314 x y
       grind)
    | exact resolve eq16 eq4314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5573 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq193 X0 X2 (σ X1)
       grind)
    | exact superpose eq193 eq15
    | (have j1 := eq193 X0 X1 (σ X2)
       grind)
    | exact resolve eq15 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq5750 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5224
       have i₂ := eq256 x y
       grind)
    | exact superpose eq256 eq5224
    | (have j1 := eq256 x y
       grind)
    | exact resolve eq5224 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5224
  have eq5755 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq5750
  have eq5756 : y = (M.op x x) := by grind
  clear eq5755
  have eq6184 : ∀ X0 : G, x ≠ y ∨ (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x X0
       have i₂ := eq5756
       grind)
    | exact superpose eq5756 eq12
    | (have j0 := eq12 x X0
       grind)
    | exact resolve eq12 eq5756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6186 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq210 x X0
       have i₂ := eq5756
       grind)
    | exact superpose eq5756 eq210
    | exact resolve eq210 eq5756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq6193 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 x
       have i₂ := eq5756
       grind)
    | exact superpose eq5756 eq9
    | exact resolve eq9 eq5756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8979 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k x X0))) ∨ (M.op x x) = X0 := by
    intro X0
    first
    | (have i₁ := eq6186 (σ X0)
       have i₂ := eq4314 x X0
       grind)
    | exact superpose eq4314 eq6186
    | (have j1 := eq4314 x X0
       grind)
    | exact resolve eq6186 eq4314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4314
  have eq9029 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq8979 X0
       have i₂ := eq5756
       grind)
    | exact superpose eq5756 eq8979
    | (have j0 := eq8979 X0
       grind)
    | exact resolve eq8979 eq5756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8979
  have eq24821 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq661 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq661
    | exact resolve eq661 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq25215 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24821 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq24821
    | (have j0 := eq24821 X0 X1
       grind)
    | exact resolve eq24821 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24821
  have eq29862 : ∀ X0 X1 X2 : G, (σ X0) = (σ X1) ∨ (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq685 X2 X1
       have i₂ := eq25215 X0 X2
       grind)
    | (have i₁ := eq685 X0 X1
       have i₂ := eq25215 (M.op X0 X0) X1
       grind)
    | exact superpose eq25215 eq685
    | (have j0 := eq685 X2 X1
       have j1 := eq25215 X0 X2
       grind)
    | exact resolve eq685 eq25215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq31291 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq121 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq31413 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq31291 (σ x) x
       have i₂ := eq6186 x
       grind)
    | exact superpose eq6186 eq31291
    | exact resolve eq31291 eq6186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6186 eq31291
  have eq32644 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq37 x (M.op (σ x) (σ y))
       have i₂ := eq31413
       grind)
    | exact superpose eq31413 eq37
    | exact resolve eq37 eq31413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq31413
  have eq39379 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq214 x X0
       have i₂ := eq5756
       grind)
    | exact superpose eq5756 eq214
    | (have j0 := eq214 x X0
       grind)
    | exact resolve eq214 eq5756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq65781 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 ∨ (M.op x x) = X0 := by
    intro X0
    first
    | (have i₁ := eq9029 X0
       have i₂ := eq25215 X0 x
       grind)
    | exact superpose eq25215 eq9029
    | (have j0 := eq9029 X0
       have j1 := eq25215 X0 x
       grind)
    | exact resolve eq9029 eq25215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9029
  have eq65954 : ∀ X0 : G, y = X0 ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq65781 X0
       have i₂ := eq5756
       grind)
    | exact superpose eq5756 eq65781
    | (have j0 := eq65781 X0
       grind)
    | exact resolve eq65781 eq5756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65781
  have eq65955 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq65954 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65954
  have eq86059 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X2)) ≠ (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5073 X1 X0 X2
       have i₂ := eq25215 X0 X1
       grind)
    | exact superpose eq25215 eq5073
    | (have j1 := eq25215 X1 X0
       grind)
    | exact resolve eq5073 eq25215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5073 eq25215
  have eq158836 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq5573 x X0 y
       grind)
    | exact superpose eq5573 eq16
    | (have j1 := eq5573 x X0 X0
       grind)
    | exact resolve eq16 eq5573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5573
  have eq158848 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq158836 X0
       have j1 := eq29862 X0 y x
       grind)
    | (have r₁ := eq158836 X0
       have r₂ := eq29862 (M.op x y) (k x y) x
       grind)
    | (have r₁ := eq158836 X0
       have r₂ := eq29862 (k x y) (M.op x y) x
       grind)
    | (have r₁ := eq158836 X0
       have r₂ := eq29862 y x x
       grind)
    | exact resolve eq158836 eq29862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29862 eq158836
  have eq158924 : ∀ X0 : G, (τ (σ (k x x))) = X0 ∨ (M.op (σ x) (σ X0)) = (k (σ x) (σ X0)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq4151 (σ x) X0
       have i₂ := eq158848 x
       grind)
    | exact superpose eq158848 eq4151
    | (have j0 := eq4151 (σ x) X0
       have j1 := eq158848 x
       grind)
    | exact resolve eq4151 eq158848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4151 eq158848
  have eq158969 : ∀ X0 : G, (τ (σ (k x x))) = X0 ∨ (M.op (σ x) (σ X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq158924 X0
       have j1 := eq39379 (σ X0)
       grind)
    | (have r₁ := eq158924 X0
       have r₂ := eq39379 X0
       grind)
    | exact resolve eq158924 eq39379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39379 eq158924
  have eq159016 : ∀ X0 : G, (k x x) = X0 ∨ (M.op (σ x) (σ X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq158969 X0
       have i₂ := eq10 (k x x)
       grind)
    | exact superpose eq10 eq158969
    | (have j0 := eq158969 X0
       grind)
    | exact resolve eq158969 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158969
  have eq159044 : ∀ X0 : G, (M.op x x) = X0 ∨ (M.op (σ x) (σ X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq159016 X0
       have i₂ := eq90 x
       grind)
    | exact superpose eq90 eq159016
    | (have j0 := eq159016 X0
       grind)
    | exact resolve eq159016 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159016
  have eq159059 : ∀ X0 : G, y = X0 ∨ (M.op (σ x) (σ X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq159044 X0
       have i₂ := eq5756
       grind)
    | exact superpose eq5756 eq159044
    | (have j0 := eq159044 X0
       grind)
    | exact resolve eq159044 eq5756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159044
  have eq159067 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq159059 X0
       have i₂ := eq15 x X0
       grind)
    | exact superpose eq15 eq159059
    | (have j0 := eq159059 X0
       grind)
    | exact resolve eq159059 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159059
  have eq159224 : ∀ X0 : G, (τ (σ (k x x))) = X0 ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq361 (σ x) X0
       have i₂ := eq159067 x
       grind)
    | exact superpose eq159067 eq361
    | (have j0 := eq361 (σ x) X0
       have j1 := eq159067 x
       grind)
    | exact resolve eq361 eq159067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361 eq159067
  have eq159292 : ∀ X0 : G, (k x x) = X0 ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq159224 X0
       have i₂ := eq10 (k x x)
       grind)
    | exact superpose eq10 eq159224
    | (have j0 := eq159224 X0
       grind)
    | exact resolve eq159224 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159224
  have eq159350 : ∀ X0 : G, (M.op x x) = X0 ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq159292 X0
       have i₂ := eq90 x
       grind)
    | exact superpose eq90 eq159292
    | (have j0 := eq159292 X0
       grind)
    | exact resolve eq159292 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq159292
  have eq159378 : ∀ X0 : G, y = X0 ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq159350 X0
       have i₂ := eq5756
       grind)
    | exact superpose eq5756 eq159350
    | (have j0 := eq159350 X0
       grind)
    | exact resolve eq159350 eq5756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159350
  have eq159394 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ y = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq159378 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq159378
    | (have j0 := eq159378 X0
       grind)
    | exact resolve eq159378 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159378
  have eq159402 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq159394 X0
       have j1 := eq6184 X0
       grind)
    | (have r₁ := eq159394 x
       have r₂ := eq6184 X0
       grind)
    | (have r₁ := eq159394 X0
       have r₂ := eq6184 X0
       grind)
    | exact resolve eq159394 eq6184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6184 eq159394
  have eq159454 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq19 X0 x
       have i₂ := eq159402 (τ X0)
       grind)
    | exact superpose eq159402 eq19
    | (have j1 := eq159402 (τ X0)
       grind)
    | exact resolve eq19 eq159402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq159402
  have eq211078 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X2)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4075 X0 X1 X1
       have i₂ := eq256 X0 X1
       grind)
    | exact superpose eq256 eq4075
    | (have j0 := eq4075 X0 X1 X1
       have j1 := eq256 X0 X1
       grind)
    | exact resolve eq4075 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256 eq4075
  have eq212168 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X2)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq211078 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211078
  have eq212175 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq212168 X0 X1 x
       have j1 := eq86059 X0 X1 x
       grind)
    | (have r₁ := eq212168 X0 X1 x
       have r₂ := eq86059 X0 X1 x
       grind)
    | exact resolve eq212168 eq86059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86059 eq212168
  have eq212270 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op x (M.op x X0))) ∨ y = X0 ∨ (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq65955 X0
       have i₂ := eq212175 x (M.op x X0)
       grind)
    | exact superpose eq212175 eq65955
    | (have j0 := eq65955 X0
       have j1 := eq212175 x (M.op x X0)
       grind)
    | exact resolve eq65955 eq212175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65955 eq212175
  have eq212553 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = X0 ∨ (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq212270 X0
       have i₂ := eq6193 X0
       grind)
    | exact superpose eq6193 eq212270
    | (have j0 := eq212270 X0
       grind)
    | exact resolve eq212270 eq6193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212270
  have eq212627 : ∀ X0 : G, y = X0 ∨ (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq212553 X0
       grind)
    | (have r₁ := eq212553 X0
       have r₂ := eq16
       grind)
    | exact resolve eq212553 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212553
  have eq212647 : ∀ X0 : G, y = (M.op x X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq212627 X0
       have i₂ := eq5756
       grind)
    | exact superpose eq5756 eq212627
    | (have j0 := eq212627 (M.op x X0)
       grind)
    | exact resolve eq212627 eq5756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5756 eq212627
  have eq213627 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq6193 X0
       have i₂ := eq212647 (M.op x X0)
       grind)
    | exact superpose eq212647 eq6193
    | (have j1 := eq212647 y
       grind)
    | exact resolve eq6193 eq212647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6193
  have eq213633 : ∀ X0 : G, (σ y) = (k (σ x) X0) ∨ (τ X0) = y ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq159454 X0
       have i₂ := eq212647 (τ X0)
       grind)
    | exact superpose eq212647 eq159454
    | (have j0 := eq159454 X0
       have j1 := eq212647 (τ X0)
       grind)
    | exact resolve eq159454 eq212647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159454 eq212647
  have eq213756 : ∀ X0 : G, (σ y) = (k (σ x) X0) ∨ (τ X0) = y := by
    intro X0
    first
    | (have j0 := eq213633 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213633
  have eq215352 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq213627 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213627
  have eq215353 : y = (M.op x y) := by grind
  clear eq215352
  have eq217576 : ∀ X0 : G, (k (τ (σ x)) X0) = (τ (σ y)) ∨ (τ (σ X0)) = y := by
    intro X0
    first
    | (have i₁ := eq23 (σ x) X0
       have i₂ := eq213756 (σ X0)
       grind)
    | exact superpose eq213756 eq23
    | (have j1 := eq213756 (σ X0)
       grind)
    | exact resolve eq23 eq213756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq213756
  have eq217619 : ∀ X0 : G, y = (k (τ (σ x)) X0) ∨ (τ (σ X0)) = y := by
    intro X0
    first
    | (have i₁ := eq217576 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq217576
    | (have j0 := eq217576 X0
       grind)
    | exact resolve eq217576 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217576
  have eq217675 : ∀ X0 : G, y = (k x X0) ∨ (τ (σ X0)) = y := by
    intro X0
    first
    | (have i₁ := eq217619 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq217619
    | (have j0 := eq217619 X0
       grind)
    | exact resolve eq217619 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217619
  have eq217691 : ∀ X0 : G, y = (k x X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq217675 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq217675
    | (have j0 := eq217675 X0
       grind)
    | exact resolve eq217675 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217675
  have eq218996 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq32644
       have i₂ := eq217691 (τ (M.op (σ x) (σ y)))
       grind)
    | exact superpose eq217691 eq32644
    | (have j1 := eq217691 (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq32644 eq217691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32644 eq217691
  have eq219119 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq218996
  have eq222113 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq219119
       grind)
    | exact superpose eq219119 eq11
    | exact resolve eq11 eq219119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219119
  have eq226119 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq222113
       grind)
    | exact superpose eq222113 eq16
    | exact resolve eq16 eq222113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222113
  have eq226240 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq226119
       have i₂ := eq215353
       grind)
    | exact superpose eq215353 eq226119
    | exact resolve eq226119 eq215353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215353 eq226119
  have eq226241 : False := by grind
  exact eq226241

/-- `Equation47`: `x = x ◇ (x ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_x_pxx_x_pxy_Equation47 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law47 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law47.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq20 (σ X0)
       grind)
    | exact superpose eq20 eq15
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22 X0
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq22
    | exact resolve eq22 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq22
  have eq36 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq36
    | (have j0 := eq36 X0 X1
       grind)
    | exact resolve eq36 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq74 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq12
    | exact resolve eq12 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq43
    | (have j0 := eq43 (σ X0) (σ X1)
       grind)
    | exact resolve eq43 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq141 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq135 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq135 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq135 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq135 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq148 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq113 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq113
    | (have j0 := eq113 X0 X1
       grind)
    | exact resolve eq113 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq313 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq317 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq313 X0 X1
       have j1 := eq148 X0 X1
       grind)
    | (have r₁ := eq313 X0 X1
       have r₂ := eq148 X0 X1
       grind)
    | exact resolve eq313 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq313
  have eq350 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq141 X0 (τ X1)
       grind)
    | exact superpose eq141 eq18
    | (have j1 := eq141 X0 (τ X1)
       grind)
    | exact resolve eq18 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq141
  have eq827 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq317 x y
       grind)
    | exact superpose eq317 eq16
    | (have j1 := eq317 x y
       grind)
    | exact resolve eq16 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq848 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq317 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq2166 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq350 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq350
    | exact resolve eq350 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq2237 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2166 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2166
    | (have j0 := eq2166 X0 X1
       grind)
    | exact resolve eq2166 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2166
  have eq3317 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq827
       have i₂ := eq2237 y x
       grind)
    | exact superpose eq2237 eq827
    | (have j1 := eq2237 (σ y) (σ x)
       grind)
    | (have r₁ := eq827
       have r₂ := eq2237 y x
       grind)
    | exact resolve eq827 eq2237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq3318 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3317
  have eq3357 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3318
       grind)
    | exact superpose eq3318 eq16
    | exact resolve eq16 eq3318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3359 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq3318
       grind)
    | exact superpose eq3318 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3318
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq3318
       grind)
    | exact resolve eq13 eq3318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3362 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3359
  have eq3365 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3362
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq3362
    | exact resolve eq3362 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3362
  have eq3369 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3365
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3365
    | exact resolve eq3365 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3365
  have eq16203 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2237 y x
       have i₂ := eq3369
       grind)
    | exact superpose eq3369 eq2237
    | (have j0 := eq2237 y x
       grind)
    | exact resolve eq2237 eq3369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3369
  have eq16283 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq16203
  have eq16315 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16283
       have r₂ := eq3357
       grind)
    | exact resolve eq16283 eq3357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16283
  have eq16764 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq16315
       grind)
    | exact superpose eq16315 eq10
    | exact resolve eq10 eq16315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16315
  have eq16857 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16764
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16764
    | exact resolve eq16764 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16764
  have eq17281 : x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq16857
       grind)
    | exact superpose eq16857 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq16857
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq16857
       grind)
    | exact resolve eq13 eq16857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17283 : x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) := by grind
  clear eq17281
  have eq17284 : x = (k x y) ∨ x = (M.op x x) := by grind
  clear eq17283
  have eq17582 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq848 x y
       have i₂ := eq17284
       grind)
    | exact superpose eq17284 eq848
    | (have j0 := eq848 x y
       grind)
    | exact resolve eq848 eq17284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17284
  have eq17604 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq17582
  have eq18215 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17604
       grind)
    | exact superpose eq17604 eq16
    | exact resolve eq16 eq17604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17604
  have eq18507 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18215
       have i₂ := eq16857
       grind)
    | exact superpose eq16857 eq18215
    | exact resolve eq18215 eq16857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16857 eq18215
  have eq18508 : (σ x) ≠ (σ x) ∨ x = (M.op x x) := by grind
  clear eq18507
  have eq18509 : x = (M.op x x) := by grind
  clear eq18508
  have eq18956 : ∀ X0 : G, x ≠ (M.op x X0) ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x x
       have i₂ := eq18509
       grind)
    | exact superpose eq18509 eq12
    | exact resolve eq12 eq18509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18959 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (σ x) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq74 x x
       have i₂ := eq18509
       grind)
    | exact superpose eq18509 eq74
    | exact resolve eq74 eq18509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq18509
  have eq19658 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18959 (σ y)
       have i₂ := eq3318
       grind)
    | exact superpose eq3318 eq18959
    | (have j0 := eq18959 (σ y)
       grind)
    | (have r₁ := eq18959 (σ y)
       have r₂ := eq3318
       grind)
    | exact resolve eq18959 eq3318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3318 eq18959
  have eq19686 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19658
  have eq19700 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19686
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq19686
    | exact resolve eq19686 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19686
  have eq20071 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2237 y x
       have i₂ := eq19700
       grind)
    | exact superpose eq19700 eq2237
    | (have j0 := eq2237 y x
       grind)
    | exact resolve eq2237 eq19700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2237
  have eq20074 : (k x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq19700
       grind)
    | exact superpose eq19700 eq10
    | exact resolve eq10 eq19700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19700
  have eq20157 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq20071
  have eq20192 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20074
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq20074
    | exact resolve eq20074 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20074
  have eq20193 : x = (M.op x y) := by
    first
    | (have r₁ := eq20157
       have r₂ := eq3357
       grind)
    | exact resolve eq20157 eq3357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3357 eq20157
  have eq20203 : x = (k x y) := by
    first
    | (have j1 := eq18956 y
       grind)
    | (have r₁ := eq20192
       have r₂ := eq18956 y
       grind)
    | exact resolve eq20192 eq18956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18956 eq20192
  have eq20676 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq848 x y
       have i₂ := eq20203
       grind)
    | exact superpose eq20203 eq848
    | (have j0 := eq848 x y
       grind)
    | exact resolve eq848 eq20203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848 eq20203
  have eq20700 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20676
  have eq21246 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20700
       grind)
    | exact superpose eq20700 eq16
    | exact resolve eq16 eq20700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20700
  have eq21264 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq21246
       have i₂ := eq20193
       grind)
    | exact superpose eq20193 eq21246
    | exact resolve eq21246 eq20193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20193 eq21246
  have eq21265 : False := by grind
  exact eq21265

/-- `Equation47`: `x = x ◇ (x ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_y_pxx_y_pxy_Equation47 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law47 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law47.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq20 (σ X0)
       grind)
    | exact superpose eq20 eq15
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22 X0
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq22
    | exact resolve eq22 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq22
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq35
    | (have j0 := eq35 X0 X1
       grind)
    | exact resolve eq35 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq67 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq42
    | (have j0 := eq42 (σ X0) (σ X1)
       grind)
    | exact resolve eq42 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq112 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq109 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq109 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq109 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq109 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq109 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq117 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq91
    | (have j0 := eq91 X0 X1
       grind)
    | exact resolve eq91 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq296 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq298 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq296 X0 X1
       have j1 := eq117 X0 X1
       grind)
    | (have r₁ := eq296 X0 X1
       have r₂ := eq117 X0 X1
       grind)
    | exact resolve eq296 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq296
  have eq330 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq112 (τ X0) X1
       grind)
    | exact superpose eq112 eq17
    | (have j1 := eq112 (τ X0) X1
       grind)
    | exact resolve eq17 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq112
  have eq876 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq298 x y
       grind)
    | exact superpose eq298 eq16
    | (have j1 := eq298 x y
       grind)
    | exact resolve eq16 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq898 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq298 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq2122 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq330 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq330
    | exact resolve eq330 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq2210 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2122 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2122
    | (have j0 := eq2122 X0 X1
       grind)
    | exact resolve eq2122 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2122
  have eq2811 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq876
       have i₂ := eq2210 x y
       grind)
    | exact superpose eq2210 eq876
    | (have j1 := eq2210 (σ x) (σ y)
       grind)
    | (have r₁ := eq876
       have r₂ := eq2210 x y
       grind)
    | exact resolve eq876 eq2210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq2812 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2811
  have eq2850 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2812
       grind)
    | exact superpose eq2812 eq16
    | exact resolve eq16 eq2812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2852 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq2812
       grind)
    | exact superpose eq2812 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2812
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2812
       grind)
    | exact resolve eq13 eq2812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2855 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2852
  have eq2856 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2855
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq2855
    | exact resolve eq2855 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2855
  have eq2860 : (σ y) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2856
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq2856
    | exact resolve eq2856 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2856
  have eq12400 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2210 x y
       have i₂ := eq2860
       grind)
    | exact superpose eq2860 eq2210
    | (have j0 := eq2210 x y
       grind)
    | exact resolve eq2210 eq2860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2210 eq2860
  have eq12478 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq12400
  have eq12510 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12478
       have r₂ := eq2850
       grind)
    | exact resolve eq12478 eq2850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2850 eq12478
  have eq12828 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq12510
       grind)
    | exact superpose eq12510 eq10
    | exact resolve eq10 eq12510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12510
  have eq12918 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12828
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq12828
    | exact resolve eq12828 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12828
  have eq13249 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq12918
       grind)
    | exact superpose eq12918 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq12918
       grind)
    | exact resolve eq13 eq12918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13251 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) := by grind
  clear eq13249
  have eq13252 : y = (k x y) ∨ y = (M.op x x) := by grind
  clear eq13251
  have eq13612 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq898 x y
       have i₂ := eq13252
       grind)
    | exact superpose eq13252 eq898
    | (have j0 := eq898 x y
       grind)
    | exact resolve eq898 eq13252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898 eq13252
  have eq13634 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq13612
  have eq14412 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13634
       grind)
    | exact superpose eq13634 eq16
    | exact resolve eq16 eq13634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13634
  have eq14467 : (σ y) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14412
       have i₂ := eq12918
       grind)
    | exact superpose eq12918 eq14412
    | exact resolve eq14412 eq12918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12918 eq14412
  have eq14468 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq14467
  have eq14469 : y = (M.op x x) := by grind
  clear eq14468
  have eq14752 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq9 x
       have i₂ := eq14469
       grind)
    | exact superpose eq14469 eq9
    | exact resolve eq9 eq14469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14758 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq67 x
       have i₂ := eq14469
       grind)
    | exact superpose eq14469 eq67
    | exact resolve eq67 eq14469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq14469
  have eq16034 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14758
       have i₂ := eq2812
       grind)
    | exact superpose eq2812 eq14758
    | exact resolve eq14758 eq2812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14758
  have eq17164 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2812
       have i₂ := eq16034
       grind)
    | exact superpose eq16034 eq2812
    | exact resolve eq2812 eq16034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2812 eq16034
  have eq17202 : y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq17164
  have eq17736 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14752
       have i₂ := eq17202
       grind)
    | exact superpose eq17202 eq14752
    | exact resolve eq14752 eq17202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14752
  have eq17886 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17202
       have i₂ := eq17736
       grind)
    | exact superpose eq17736 eq17202
    | exact resolve eq17202 eq17736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17202 eq17736
  have eq17896 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq17886
  have eq18307 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq17896
       grind)
    | exact superpose eq17896 eq10
    | exact resolve eq10 eq17896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17896
  have eq18407 : x = y ∨ x = y := by
    first
    | (have i₁ := eq18307
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18307
    | exact resolve eq18307 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18307
  have eq18408 : x = y := by grind
  clear eq18407
  have eq18932 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18408
       grind)
    | exact superpose eq18408 eq16
    | exact resolve eq16 eq18408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18408
  have eq18963 : False := by grind
  exact eq18963

/-- `Equation47`: `x = x ◇ (x ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_pxx_pxy_Equation47 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law47 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law47.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq15
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq104 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq107 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq104 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq104 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq104 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq104 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq104 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq175 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq107 (σ X0) (σ X1)
       grind)
    | exact superpose eq107 eq15
    | (have j1 := eq107 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq107 X0 (τ X1)
       grind)
    | exact superpose eq107 eq19
    | (have j1 := eq107 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq107
  have eq814 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq178
    | exact resolve eq178 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq854 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq814 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq814
    | (have j0 := eq814 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq814 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq2091 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq175 x y
       grind)
    | exact superpose eq175 eq16
    | (have j1 := eq175 x y
       grind)
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq2142 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2091
       have i₂ := eq854 y x
       grind)
    | exact superpose eq854 eq2091
    | (have j1 := eq854 (σ x) (σ y)
       grind)
    | (have r₁ := eq2091
       have r₂ := eq854 y x
       grind)
    | (have r₁ := eq2091
       have r₂ := eq854 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2091
       have r₂ := eq854 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2091 eq854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854 eq2091
  have eq2143 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2142
  have eq2214 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2143
       grind)
    | exact superpose eq2143 eq10
    | exact resolve eq10 eq2143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143
  have eq2261 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2214
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2214
    | exact resolve eq2214 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2214
  have eq2262 : x = y := by grind
  clear eq2261
  have eq2292 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2262
       grind)
    | exact superpose eq2262 eq16
    | exact resolve eq16 eq2262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2262
  have eq2293 : False := by grind
  exact eq2293

/-- `Equation47`: `x = x ◇ (x ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_x_pxy_Equation47 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law47 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law47.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq15
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq104 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq107 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq104 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq104 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq104 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq104 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq104 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq175 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq107 (σ X0) (σ X1)
       grind)
    | exact superpose eq107 eq15
    | (have j1 := eq107 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq107 X0 (τ X1)
       grind)
    | exact superpose eq107 eq19
    | (have j1 := eq107 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq107
  have eq814 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq178
    | exact resolve eq178 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq854 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq814 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq814
    | (have j0 := eq814 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq814 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq2091 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq175 x y
       grind)
    | exact superpose eq175 eq16
    | (have j1 := eq175 x y
       grind)
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq2142 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2091
       have i₂ := eq854 y x
       grind)
    | exact superpose eq854 eq2091
    | (have j1 := eq854 (σ x) (σ y)
       grind)
    | (have r₁ := eq2091
       have r₂ := eq854 y x
       grind)
    | (have r₁ := eq2091
       have r₂ := eq854 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2091
       have r₂ := eq854 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2091 eq854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854 eq2091
  have eq2143 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2142
  have eq2214 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2143
       grind)
    | exact superpose eq2143 eq10
    | exact resolve eq10 eq2143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143
  have eq2261 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2214
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2214
    | exact resolve eq2214 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2214
  have eq2262 : x = y := by grind
  clear eq2261
  have eq2292 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2262
       grind)
    | exact superpose eq2262 eq16
    | exact resolve eq16 eq2262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2262
  have eq2293 : False := by grind
  exact eq2293

/-- `Equation47`: `x = x ◇ (x ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxy_x_pxy_Equation47 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law47 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law47.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq20 (σ X0)
       grind)
    | exact superpose eq20 eq15
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22 X0
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq22
    | exact resolve eq22 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq22
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq33 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq33 (σ X0) (σ X1)
       grind)
    | exact superpose eq33 eq15
    | (have j1 := eq33 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq33 X0 (τ X1)
       grind)
    | exact superpose eq33 eq19
    | (have j1 := eq33 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq33
  have eq185 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq59
    | exact resolve eq59 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq207 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq185 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq185
    | (have j0 := eq185 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq185 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq568 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58 x y
       grind)
    | exact superpose eq58 eq16
    | (have j1 := eq58 x y
       grind)
    | exact resolve eq16 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq710 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq568
       have i₂ := eq207 y x
       grind)
    | exact superpose eq207 eq568
    | (have j1 := eq207 (σ x) (σ y)
       grind)
    | (have r₁ := eq568
       have r₂ := eq207 y x
       grind)
    | (have r₁ := eq568
       have r₂ := eq207 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq568
       have r₂ := eq207 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq568 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq568
  have eq711 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq710
  have eq811 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq711
       grind)
    | exact superpose eq711 eq10
    | exact resolve eq10 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq847 : x = y ∨ x = y := by
    first
    | (have i₁ := eq811
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq811
    | exact resolve eq811 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq848 : x = y := by grind
  clear eq847
  have eq1022 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq848
       grind)
    | exact superpose eq848 eq16
    | exact resolve eq16 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq1023 : False := by grind
  exact eq1023

/-- `Equation47`: `x = x ◇ (x ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pxy_Equation47 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law47 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law47.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq20 (σ X0)
       grind)
    | exact superpose eq20 eq15
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22 X0
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq22
    | exact resolve eq22 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq22
  have eq28 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ X1 = X2 ∨ (k X0 X2) = (M.op X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X2
       have i₂ := eq14 X1 X2
       grind)
    | (have i₁ := eq14 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | (have j0 := eq14 X1 X2
       have j1 := eq14 X1 X2
       grind)
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq14 X0 X2
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 X2 : G, (k X1 X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ X1 = X2 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq28 X1 X1 X2
       have j1 := eq34 X1 X1 X2
       grind)
    | (have r₁ := eq28 X0 X1 X2
       have r₂ := eq34 X0 X1 X2
       grind)
    | (have r₁ := eq28 X1 X0 X2
       have r₂ := eq34 X0 X1 X2
       grind)
    | (have r₁ := eq28 X0 (M.op X0 X0) (M.op X1 X1)
       have r₂ := eq34 X0 X1 X2
       grind)
    | exact resolve eq28 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq34
  have eq168 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq169 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq168 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq170 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq169 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq174 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq170 (σ X0) (σ X1)
       grind)
    | exact superpose eq170 eq15
    | (have j1 := eq170 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq170 X0 (τ X1)
       grind)
    | exact superpose eq170 eq19
    | (have j1 := eq170 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq170
  have eq715 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq177
    | exact resolve eq177 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq749 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq715 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq715
    | (have j0 := eq715 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq715 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq1759 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq174 x y
       grind)
    | exact superpose eq174 eq16
    | (have j1 := eq174 x y
       grind)
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq2014 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1759
       have i₂ := eq749 y x
       grind)
    | exact superpose eq749 eq1759
    | (have j1 := eq749 (σ x) (σ y)
       grind)
    | (have r₁ := eq1759
       have r₂ := eq749 y x
       grind)
    | (have r₁ := eq1759
       have r₂ := eq749 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1759
       have r₂ := eq749 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1759 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749 eq1759
  have eq2015 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2014
  have eq2270 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2015
       grind)
    | exact superpose eq2015 eq10
    | exact resolve eq10 eq2015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2015
  have eq2316 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2270
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2270
    | exact resolve eq2270 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2270
  have eq2317 : x = y := by grind
  clear eq2316
  have eq2580 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2317
       grind)
    | exact superpose eq2317 eq16
    | exact resolve eq16 eq2317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2317
  have eq2581 : False := by grind
  exact eq2581

/-- `Equation47`: `x = x ◇ (x ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation47 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law47 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law47.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq84 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35 x y
       grind)
    | exact superpose eq35 eq16
    | (have j1 := eq35 x y
       grind)
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq391 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (τ X1) (τ X0)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq90
    | (have j0 := eq90 (τ X1) (τ X0)
       grind)
    | exact resolve eq90 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq398 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq391 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq391
    | (have j0 := eq391 X0 X1
       grind)
    | exact resolve eq391 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq401 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq398 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq398
    | (have j0 := eq398 X0 X1
       grind)
    | exact resolve eq398 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq403 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq401 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq401
    | (have j0 := eq401 X0 X1
       grind)
    | exact resolve eq401 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq404 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq403 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq403
    | (have j0 := eq403 X0 X1
       grind)
    | exact resolve eq403 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq405 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq404 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq404
    | (have j0 := eq404 X0 X1
       grind)
    | exact resolve eq404 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq406 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq405 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq405
    | (have j0 := eq405 X0 X1
       grind)
    | exact resolve eq405 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq456 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (τ X1) (τ X0)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq91
    | (have j0 := eq91 (τ X1) (τ X0)
       grind)
    | exact resolve eq91 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq464 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq456 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq456
    | (have j0 := eq456 X0 X1
       grind)
    | exact resolve eq456 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq467 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq464 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq464
    | (have j0 := eq464 X0 X1
       grind)
    | exact resolve eq464 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq469 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq467 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq467
    | (have j0 := eq467 X0 X1
       grind)
    | exact resolve eq467 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq470 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq469 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq469
    | (have j0 := eq469 X0 X1
       grind)
    | exact resolve eq469 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq471 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq470 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq470
    | (have j0 := eq470 X0 X1
       grind)
    | exact resolve eq470 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq472 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq471 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq471
    | (have j0 := eq471 X0 X1
       grind)
    | exact resolve eq471 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq482 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq84
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq84 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq483 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq482
  have eq3776 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq483
       grind)
    | exact superpose eq483 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq483
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq483
       grind)
    | exact resolve eq12 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq3778 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq3776
  have eq3779 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3778
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3778
    | exact resolve eq3778 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3778
  have eq23990 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq3779
       grind)
    | exact superpose eq3779 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3779
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3779
       grind)
    | exact resolve eq13 eq3779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23991 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq3779
       grind)
    | exact superpose eq3779 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3779
       grind)
    | exact resolve eq12 eq3779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3779
  have eq23992 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq23990
  have eq23995 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23991
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq23991
    | exact resolve eq23991 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23991
  have eq23996 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq23995
  have eq23997 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23992
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq23992
    | exact resolve eq23992 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23992
  have eq23999 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq23997
       have r₂ := eq23996
       grind)
    | exact resolve eq23997 eq23996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23996 eq23997
  have eq24805 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq23999
       grind)
    | exact superpose eq23999 eq10
    | exact resolve eq10 eq23999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23999
  have eq24963 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq24805
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq24805
    | exact resolve eq24805 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24805
  have eq24966 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq472 y x
       grind)
    | (have r₁ := eq24963
       have r₂ := eq472 y x
       grind)
    | exact resolve eq24963 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472 eq24963
  have eq25056 : (k y x) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq24966
       grind)
    | exact superpose eq24966 eq10
    | exact resolve eq10 eq24966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24966
  have eq25215 : x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25056
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq25056
    | exact resolve eq25056 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25056
  have eq25216 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq406 y x
       grind)
    | (have r₁ := eq25215
       have r₂ := eq406 y x
       grind)
    | exact resolve eq25215 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq25215
  have eq25303 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq25216
       grind)
    | exact superpose eq25216 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq25216
       grind)
    | exact resolve eq12 eq25216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25304 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq25305 : x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq25303
  have eq25836 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90 x y
       have i₂ := eq25305
       grind)
    | exact superpose eq25305 eq90
    | (have j0 := eq90 x y
       grind)
    | exact resolve eq90 eq25305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq25881 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq25836
  have eq32854 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25881
       grind)
    | exact superpose eq25881 eq16
    | exact resolve eq16 eq25881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25881
  have eq33546 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32854
       have i₂ := eq25216
       grind)
    | exact superpose eq25216 eq32854
    | exact resolve eq32854 eq25216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32854
  have eq33549 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq33546
  have eq33550 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq33549
       have r₂ := eq25304
       grind)
    | exact resolve eq33549 eq25304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33549
  have eq33916 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33550
       grind)
    | exact superpose eq33550 eq16
    | exact resolve eq16 eq33550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33917 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq33550
       grind)
    | exact superpose eq33550 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq33550
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq33550
       grind)
    | exact resolve eq13 eq33550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33550
  have eq33919 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq33917
  have eq33923 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq33919
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq33919
    | exact resolve eq33919 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33919
  have eq34281 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq33916
       have i₂ := eq25216
       grind)
    | exact superpose eq25216 eq33916
    | exact resolve eq33916 eq25216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25216 eq33916
  have eq34285 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq34281
       have r₂ := eq25304
       grind)
    | exact resolve eq34281 eq25304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25304 eq34281
  have eq35374 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq33923
       have i₂ := eq25305
       grind)
    | exact superpose eq25305 eq33923
    | exact resolve eq33923 eq25305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25305 eq33923
  have eq35524 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq35374
  have eq35653 : x = (M.op x y) := by
    first
    | (have r₁ := eq35524
       have r₂ := eq34285
       grind)
    | exact resolve eq35524 eq34285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34285 eq35524
  have eq36086 : x ≠ x ∨ x = y ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq35653
       grind)
    | exact superpose eq35653 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq35653
       grind)
    | exact resolve eq13 eq35653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36087 : x ≠ y ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq35653
       grind)
    | exact superpose eq35653 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq35653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36088 : y = (k y x) ∨ x = y := by grind
  clear eq36086
  have eq36814 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq91 x y
       have i₂ := eq36088
       grind)
    | exact superpose eq36088 eq91
    | (have j0 := eq91 x y
       grind)
    | exact resolve eq91 eq36088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq36840 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq36814
  have eq39082 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq36840
       grind)
    | exact superpose eq36840 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq36840
       grind)
    | exact resolve eq12 eq36840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36840
  have eq39084 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq39082
  have eq39085 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq39084
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq39084
    | exact resolve eq39084 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39084
  have eq40284 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq39085
       grind)
    | exact superpose eq39085 eq16
    | exact resolve eq16 eq39085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39085
  have eq40293 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq40284
       have i₂ := eq35653
       grind)
    | exact superpose eq35653 eq40284
    | exact resolve eq40284 eq35653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40284
  have eq40294 : (σ x) = (σ (k y x)) ∨ x = y := by grind
  clear eq40293
  have eq40848 : (k y x) = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq40294
       grind)
    | exact superpose eq40294 eq10
    | exact resolve eq10 eq40294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40294
  have eq41050 : x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq40848
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq40848
    | exact resolve eq40848 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40848
  have eq41051 : x = (k y x) := by
    first
    | (have r₁ := eq41050
       have r₂ := eq36087
       grind)
    | exact resolve eq41050 eq36087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36087 eq41050
  have eq41529 : x = y ∨ x = y := by
    first
    | (have i₁ := eq36088
       have i₂ := eq41051
       grind)
    | exact superpose eq41051 eq36088
    | exact resolve eq36088 eq41051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36088
  have eq41560 : x = y := by grind
  clear eq41529
  have eq41985 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41560
       grind)
    | exact superpose eq41560 eq16
    | exact resolve eq16 eq41560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41986 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq84
       have i₂ := eq41560
       grind)
    | exact superpose eq41560 eq84
    | exact resolve eq84 eq41560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq42018 : x = (M.op x x) := by
    first
    | (have i₁ := eq35653
       have i₂ := eq41560
       grind)
    | exact superpose eq41560 eq35653
    | exact resolve eq35653 eq41560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35653
  have eq42020 : x = (k x x) := by
    first
    | (have i₁ := eq41051
       have i₂ := eq41560
       grind)
    | exact superpose eq41560 eq41051
    | exact resolve eq41051 eq41560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41051 eq41560
  have eq42049 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq41986
  have eq42050 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq42049
       have i₂ := eq42020
       grind)
    | exact superpose eq42020 eq42049
    | exact resolve eq42049 eq42020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42020 eq42049
  have eq42051 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq41985
       have i₂ := eq42018
       grind)
    | exact superpose eq42018 eq41985
    | exact resolve eq41985 eq42018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41985
  have eq42052 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq42050
       have i₂ := eq42018
       grind)
    | exact superpose eq42018 eq42050
    | exact resolve eq42050 eq42018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42018 eq42050
  have eq42053 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq42052
  have eq42054 : False := by grind
  exact eq42054

/-- `Equation47`: `x = x ◇ (x ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation47 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law47 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law47.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq45 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
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
  clear eq19
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq78 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46 x y
       grind)
    | exact superpose eq46 eq16
    | (have j1 := eq46 x y
       grind)
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq339 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45
    | exact resolve eq45 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq368 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq339 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq339
    | (have j0 := eq339 X0 X1
       grind)
    | exact resolve eq339 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq748 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq78
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq78
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq78
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq78
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq78 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq749 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq748
  have eq4339 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq749
       grind)
    | exact superpose eq749 eq16
    | exact resolve eq16 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4340 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq749
       grind)
    | exact superpose eq749 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq749
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq749
       grind)
    | exact resolve eq13 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq4341 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4340
  have eq4342 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4341
  have eq4344 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4342
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq4342
    | exact resolve eq4342 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4342
  have eq8030 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq368 y x
       have i₂ := eq4344
       grind)
    | exact superpose eq4344 eq368
    | (have j0 := eq368 y x
       grind)
    | exact resolve eq368 eq4344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq8032 : (k x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq4344
       grind)
    | exact superpose eq4344 eq10
    | exact resolve eq10 eq4344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4344
  have eq8072 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq8030
  have eq8099 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8032
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8032
    | exact resolve eq8032 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8032
  have eq8100 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8072
       have r₂ := eq4339
       grind)
    | exact resolve eq8072 eq4339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4339 eq8072
  have eq8103 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq8099
       have r₂ := eq13 x y
       grind)
    | exact resolve eq8099 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8099
  have eq8523 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq80 x y
       have i₂ := eq8103
       grind)
    | exact superpose eq8103 eq80
    | (have j0 := eq80 x y
       grind)
    | exact resolve eq80 eq8103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq8103
  have eq8526 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8523
  have eq8527 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8526
  have eq8718 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq8527
       grind)
    | exact superpose eq8527 eq16
    | exact resolve eq16 eq8527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8527
  have eq8951 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8718
       have i₂ := eq8100
       grind)
    | exact superpose eq8100 eq8718
    | exact resolve eq8718 eq8100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8100 eq8718
  have eq8952 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8951
  have eq8953 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq8952
  have eq9206 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8953
       grind)
    | exact superpose eq8953 eq10
    | exact resolve eq10 eq8953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8953
  have eq9279 : x = y ∨ x = y := by
    first
    | (have i₁ := eq9206
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9206
    | exact resolve eq9206 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9206
  have eq9280 : x = y := by grind
  clear eq9279
  have eq9492 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9280
       grind)
    | exact superpose eq9280 eq16
    | exact resolve eq16 eq9280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9280
  have eq9493 : False := by grind
  exact eq9493

/-- `Equation56`: `x = x ◇ (y ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_x_pxy_Equation56 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law56 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law56.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
  have eq27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq26
    | exact resolve eq26 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq26
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq116 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq119 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq116 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq116 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq116 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq116 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq116 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq225 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq119 (σ X0) (σ X1)
       grind)
    | exact superpose eq119 eq15
    | (have j1 := eq119 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 X0
       have i₂ := eq119 X0 (τ X1)
       grind)
    | exact superpose eq119 eq21
    | (have j1 := eq119 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq21 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq119
  have eq5786 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq229 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq229
    | exact resolve eq229 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq5863 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5786 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5786
    | (have j0 := eq5786 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq5786 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5786
  have eq12462 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq225 x y
       grind)
    | exact superpose eq225 eq16
    | (have j1 := eq225 x y
       grind)
    | exact resolve eq16 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq12762 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12462
       have i₂ := eq5863 y x
       grind)
    | exact superpose eq5863 eq12462
    | (have j1 := eq5863 (σ x) (σ y)
       grind)
    | (have r₁ := eq12462
       have r₂ := eq5863 y x
       grind)
    | (have r₁ := eq12462
       have r₂ := eq5863 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq12462
       have r₂ := eq5863 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq12462 eq5863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5863 eq12462
  have eq12763 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq12762
  have eq12962 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq12763
       grind)
    | exact superpose eq12763 eq10
    | exact resolve eq10 eq12763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12763
  have eq13023 : x = y ∨ x = y := by
    first
    | (have i₁ := eq12962
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12962
    | exact resolve eq12962 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12962
  have eq13024 : x = y := by grind
  clear eq13023
  have eq13065 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13024
       grind)
    | exact superpose eq13024 eq16
    | exact resolve eq16 eq13024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13024
  have eq13066 : False := by grind
  exact eq13066

/-- `Equation56`: `x = x ◇ (y ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxx_x_pxx_pxx_pyx_Equation56 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law56 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law56.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X1))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq23 (σ X0)
       grind)
    | exact superpose eq23 eq15
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq28
    | exact resolve eq28 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq28
  have eq45 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
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
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq59 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq29 X1
       grind)
    | exact superpose eq29 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq62 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 X1
       have i₂ := eq29 X1
       grind)
    | exact superpose eq29 eq59
    | (have j0 := eq59 X0 X1
       grind)
    | exact resolve eq59 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq92 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq29 X0
       grind)
    | exact superpose eq29 eq9
    | exact resolve eq9 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq55
    | (have j0 := eq55 (σ X0) X1
       grind)
    | exact resolve eq55 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq152 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq146 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq146 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq146 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq146 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq159 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq122 X0 X1
       have i₂ := eq29 X0
       grind)
    | exact superpose eq29 eq122
    | (have j0 := eq122 X0 X1
       grind)
    | exact resolve eq122 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq166 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq159 X0 X1
       have i₂ := eq29 X0
       grind)
    | exact superpose eq29 eq159
    | (have j0 := eq159 X0 X1
       grind)
    | exact resolve eq159 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq445 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq92 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq9 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq9 eq92
    | exact resolve eq92 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq486 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq445 X0 X1
       have i₂ := eq29 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq29 eq445
    | exact resolve eq445 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq445
  have eq495 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq486 X0 X1
       have i₂ := eq9 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq9 eq486
    | exact resolve eq486 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq575 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq579 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq575 X0 X1
       have j1 := eq166 X1 X0
       grind)
    | (have r₁ := eq575 X1 X0
       have r₂ := eq166 X0 X1
       grind)
    | exact resolve eq575 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq575
  have eq699 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq152 X1 (τ X0)
       grind)
    | exact superpose eq152 eq20
    | (have j1 := eq152 X1 X1
       grind)
    | exact resolve eq20 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq152
  have eq1617 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq579 X1 X0
       grind)
    | exact superpose eq579 eq10
    | (have j1 := eq579 X1 X0
       grind)
    | exact resolve eq10 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq1651 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1617 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1617
    | (have j0 := eq1617 X0 X1
       grind)
    | exact resolve eq1617 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1617
  have eq18652 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq699 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq699
    | (have j0 := eq699 X0 X1
       grind)
    | exact resolve eq699 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq18992 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18652 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq18652
    | (have j0 := eq18652 X0 X1
       grind)
    | exact resolve eq18652 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18652
  have eq19504 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1651 y x
       grind)
    | exact superpose eq1651 eq16
    | (have j1 := eq1651 y x
       grind)
    | exact resolve eq16 eq1651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1651
  have eq19667 : y = (M.op y y) := by
    first
    | (have j1 := eq18992 x y
       grind)
    | (have r₁ := eq19504
       have r₂ := eq18992 x y
       grind)
    | exact resolve eq19504 eq18992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18992 eq19504
  have eq19799 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq19667
       grind)
    | exact superpose eq19667 eq9
    | exact resolve eq9 eq19667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19812 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq495 y X0
       have i₂ := eq19667
       grind)
    | exact superpose eq19667 eq495
    | exact resolve eq495 eq19667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq19863 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq19812 X0
       have i₂ := eq19667
       grind)
    | exact superpose eq19667 eq19812
    | exact resolve eq19812 eq19667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19812
  have eq19873 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq19799 X0
       have i₂ := eq19667
       grind)
    | exact superpose eq19667 eq19799
    | exact resolve eq19799 eq19667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19667 eq19799
  have eq20928 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19863 (σ x)
       grind)
    | exact superpose eq19863 eq16
    | exact resolve eq16 eq19863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19863
  have eq20961 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq20928
       have i₂ := eq19873 x
       grind)
    | exact superpose eq19873 eq20928
    | exact resolve eq20928 eq19873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19873 eq20928
  have eq20962 : False := by grind
  exact eq20962

/-- `Equation56`: `x = x ◇ (y ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(X,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxx_x_pxx_x_pyx_Equation56 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law56 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law56.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X1))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq23 (σ X0)
       grind)
    | exact superpose eq23 eq15
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq28
    | exact resolve eq28 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq28
  have eq45 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
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
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq59 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq29 X1
       grind)
    | exact superpose eq29 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq62 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 X1
       have i₂ := eq29 X1
       grind)
    | exact superpose eq29 eq59
    | (have j0 := eq59 X0 X1
       grind)
    | exact resolve eq59 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq92 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq29 X0
       grind)
    | exact superpose eq29 eq9
    | exact resolve eq9 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq55
    | (have j0 := eq55 (σ X0) X1
       grind)
    | exact resolve eq55 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq151 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq145 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq145 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq145 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq145 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq158 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq121 X0 X1
       have i₂ := eq29 X0
       grind)
    | exact superpose eq29 eq121
    | (have j0 := eq121 X0 X1
       grind)
    | exact resolve eq121 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq163 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq158 X0 X1
       have i₂ := eq29 X0
       grind)
    | exact superpose eq29 eq158
    | (have j0 := eq158 X0 X1
       grind)
    | exact resolve eq158 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq441 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq92 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq9 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq9 eq92
    | exact resolve eq92 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq482 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq441 X0 X1
       have i₂ := eq29 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq29 eq441
    | exact resolve eq441 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq441
  have eq491 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq482 X0 X1
       have i₂ := eq9 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq9 eq482
    | exact resolve eq482 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq571 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq575 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq571 X0 X1
       have j1 := eq163 X1 X0
       grind)
    | (have r₁ := eq571 X1 X0
       have r₂ := eq163 X0 X1
       grind)
    | exact resolve eq571 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq571
  have eq695 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq151 X1 (τ X0)
       grind)
    | exact superpose eq151 eq20
    | (have j1 := eq151 X1 X1
       grind)
    | exact resolve eq20 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq151
  have eq1612 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq575 X1 X0
       grind)
    | exact superpose eq575 eq10
    | (have j1 := eq575 X1 X0
       grind)
    | exact resolve eq10 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq1646 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1612 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1612
    | (have j0 := eq1612 X0 X1
       grind)
    | exact resolve eq1612 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612
  have eq18634 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq695 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq695
    | (have j0 := eq695 X0 X1
       grind)
    | exact resolve eq695 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq18974 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18634 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq18634
    | (have j0 := eq18634 X0 X1
       grind)
    | exact resolve eq18634 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18634
  have eq19486 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1646 y x
       grind)
    | exact superpose eq1646 eq16
    | (have j1 := eq1646 y x
       grind)
    | exact resolve eq16 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq19649 : y = (M.op y y) := by
    first
    | (have j1 := eq18974 x y
       grind)
    | (have r₁ := eq19486
       have r₂ := eq18974 x y
       grind)
    | exact resolve eq19486 eq18974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18974 eq19486
  have eq19781 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq19649
       grind)
    | exact superpose eq19649 eq9
    | exact resolve eq9 eq19649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19794 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq491 y X0
       have i₂ := eq19649
       grind)
    | exact superpose eq19649 eq491
    | exact resolve eq491 eq19649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq19845 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq19794 X0
       have i₂ := eq19649
       grind)
    | exact superpose eq19649 eq19794
    | exact resolve eq19794 eq19649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19794
  have eq19855 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq19781 X0
       have i₂ := eq19649
       grind)
    | exact superpose eq19649 eq19781
    | exact resolve eq19781 eq19649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19649 eq19781
  have eq20773 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19845 (σ x)
       grind)
    | exact superpose eq19845 eq16
    | exact resolve eq16 eq19845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19845
  have eq20805 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq20773
       have i₂ := eq19855 x
       grind)
    | exact superpose eq19855 eq20773
    | exact resolve eq20773 eq19855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19855 eq20773
  have eq20806 : False := by grind
  exact eq20806

/-- `Equation56`: `x = x ◇ (y ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxy_x_pxy_Equation56 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law56 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law56.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
  have eq29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq28
    | exact resolve eq28 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq28
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq43 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq43 (σ X0) (σ X1)
       grind)
    | exact superpose eq43 eq15
    | (have j1 := eq43 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 X0
       have i₂ := eq43 X0 (τ X1)
       grind)
    | exact superpose eq43 eq21
    | (have j1 := eq43 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq21 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq43
  have eq189 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq69
    | exact resolve eq69 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq211 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq189 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq189
    | (have j0 := eq189 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq189 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq621 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68 x y
       grind)
    | exact superpose eq68 eq16
    | (have j1 := eq68 x y
       grind)
    | exact resolve eq16 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq2682 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq621
       have i₂ := eq211 y x
       grind)
    | exact superpose eq211 eq621
    | (have j1 := eq211 (σ x) (σ y)
       grind)
    | (have r₁ := eq621
       have r₂ := eq211 y x
       grind)
    | (have r₁ := eq621
       have r₂ := eq211 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq621
       have r₂ := eq211 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq621 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq621
  have eq2683 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2682
  have eq2687 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2683
       grind)
    | exact superpose eq2683 eq10
    | exact resolve eq10 eq2683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2683
  have eq2729 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2687
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2687
    | exact resolve eq2687 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2687
  have eq2730 : x = y := by grind
  clear eq2729
  have eq2807 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2730
       grind)
    | exact superpose eq2730 eq16
    | exact resolve eq16 eq2730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2730
  have eq2808 : False := by grind
  exact eq2808

/-- `Equation56`: `x = x ◇ (y ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then X else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_pyx_x_pxx_pyx_Equation56 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law56 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law56.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X1))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq22 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq10
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq28 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq52 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq28 (σ X0)
       grind)
    | exact superpose eq28 eq15
    | (have j1 := eq28 (σ X0)
       grind)
    | exact resolve eq15 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq177 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq183 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq177 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq177 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq177 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq177 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq204 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq183 X1 (τ X0)
       grind)
    | exact superpose eq183 eq22
    | (have j1 := eq183 X1 X1
       grind)
    | exact resolve eq22 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq183 X0 X2
       grind)
    | exact superpose eq183 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq183 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq183 X0 X1
       grind)
    | exact resolve eq12 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq214 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq212 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq296 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ X0) X1) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X0 X1
       have i₂ := eq214 X0 (σ X1) X2
       grind)
    | exact superpose eq214 eq26
    | (have j1 := eq214 (τ X0) X1 X2
       grind)
    | exact resolve eq26 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq214
  have eq751 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X1)) = (k (τ (σ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq296 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq296 eq15
    | (have j1 := eq296 (σ X1) X2 X2
       grind)
    | exact resolve eq15 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq763 : ∀ X0 X1 X2 : G, (k X1 X2) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq751 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq751
    | (have j0 := eq751 X0 X1 X2
       grind)
    | exact resolve eq751 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq1604 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq68 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq4416 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq204 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq204
    | (have j0 := eq204 X0 X1
       grind)
    | exact resolve eq204 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq4534 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4416 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4416
    | (have j0 := eq4416 X0 X1
       grind)
    | exact resolve eq4416 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4416
  have eq4943 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq4534 X2 X0
       grind)
    | exact superpose eq4534 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq4534 X2 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq4534 X0 X1
       grind)
    | exact resolve eq12 eq4534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4534
  have eq4950 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4943 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4943
  have eq6129 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1604 (τ X0)
       have i₂ := eq22 X0 (τ X0)
       grind)
    | exact superpose eq22 eq1604
    | (have j0 := eq1604 (τ X0)
       grind)
    | exact resolve eq1604 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq6149 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6129 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6129
    | (have j0 := eq6129 X0
       grind)
    | exact resolve eq6129 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6129
  have eq6157 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6149 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6149
    | (have j0 := eq6149 X0
       grind)
    | exact resolve eq6149 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6149
  have eq12780 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq763 x y X0
       grind)
    | exact superpose eq763 eq16
    | (have j1 := eq763 X0 y X0
       grind)
    | exact resolve eq16 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq12862 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have j0 := eq12780 X0
       have j1 := eq4950 y X0 x
       grind)
    | (have r₁ := eq12780 X0
       have r₂ := eq4950 y x x
       grind)
    | exact resolve eq12780 eq4950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4950 eq12780
  have eq13336 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1604 y
       have i₂ := eq12862 y
       grind)
    | exact superpose eq12862 eq1604
    | (have j0 := eq1604 y
       grind)
    | exact resolve eq1604 eq12862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604
  have eq13338 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq6157 y
       have i₂ := eq12862 y
       grind)
    | exact superpose eq12862 eq6157
    | (have j0 := eq6157 y
       grind)
    | (have r₁ := eq6157 y
       have r₂ := eq12862 y
       grind)
    | exact resolve eq6157 eq12862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6157 eq12862
  have eq13394 : y = (M.op y y) := by grind
  clear eq13338
  have eq13395 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq13336
  have eq13784 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq13394
       grind)
    | exact superpose eq13394 eq9
    | exact resolve eq9 eq13394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13801 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq13784 X0
       have i₂ := eq13394
       grind)
    | exact superpose eq13394 eq13784
    | exact resolve eq13784 eq13394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13394 eq13784
  have eq15553 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y)
       have i₂ := eq13395
       grind)
    | exact superpose eq13395 eq9
    | exact resolve eq9 eq13395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15572 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq15553 X0
       have i₂ := eq13395
       grind)
    | exact superpose eq13395 eq15553
    | exact resolve eq15553 eq13395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13395 eq15553
  have eq15947 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15572 (σ x)
       grind)
    | exact superpose eq15572 eq16
    | exact resolve eq16 eq15572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15572
  have eq15959 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq15947
       have i₂ := eq13801 x
       grind)
    | exact superpose eq13801 eq15947
    | exact resolve eq15947 eq13801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13801 eq15947
  have eq15960 : False := by grind
  exact eq15960

/-- `Equation56`: `x = x ◇ (y ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_pxx_pxy_Equation56 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law56 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law56.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X1))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq27 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X1 (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq9 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X1 (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq13 X0 (M.op X1 (M.op X1 X1))
       have r₂ := eq9 (M.op X1 (M.op X1 X1)) X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 (M.op X0 X0))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq42 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 X2
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq51 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq43 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq43 X0 (M.op X0 X0) X2
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq43 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq52 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq47 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq47 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq47 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq54 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq68 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq51 X0 X0 X2
       grind)
    | exact superpose eq51 eq9
    | (have j1 := eq51 X0 X1 X2
       grind)
    | exact resolve eq9 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq52 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq106 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq105 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq109 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq106 (σ X0)
       grind)
    | exact superpose eq106 eq15
    | exact resolve eq15 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq109 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq109
    | exact resolve eq109 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq147 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq106 (τ X0)
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq106
    | exact resolve eq106 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq152 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq147 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq147
    | exact resolve eq147 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq147
  have eq169 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X1 X1))) ≠ X0 ∨ (k X0 X2) = (M.op X0 X2) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X2
       have i₂ := eq28 X1 X0
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 X0 X2
       have j1 := eq28 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq194 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X1 X1))) ≠ X0 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq169 X0 X1 X2
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq169 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq169 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq210 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq118 X0
       grind)
    | exact superpose eq118 eq9
    | exact resolve eq9 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : ∀ X0 X1 : G, (M.op X1 (M.op (τ X0) (τ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0)
       have i₂ := eq152 X0
       grind)
    | exact superpose eq152 eq9
    | exact resolve eq9 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq210 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq9 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq9 eq210
    | exact resolve eq210 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq501 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq465 X0 X1
       have i₂ := eq118 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq118 eq465
    | exact resolve eq465 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq465
  have eq509 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq501 X0 X1
       have i₂ := eq9 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq9 eq501
    | exact resolve eq501 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq637 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq509 X0 X1
       have i₂ := eq51 X0 X0 X2
       grind)
    | exact superpose eq51 eq509
    | (have j1 := eq51 X0 X1 X2
       grind)
    | exact resolve eq509 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq509
  have eq837 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (M.op X0 (M.op X0 X0))) (τ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq358 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq9 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq9 eq358
    | exact resolve eq358 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq890 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq837 X0 X1
       have i₂ := eq152 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq152 eq837
    | exact resolve eq837 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq837
  have eq902 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq890 X0 X1
       have i₂ := eq9 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq9 eq890
    | exact resolve eq890 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq947 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq68 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq68 eq15
    | (have j1 := eq68 (σ X1) X2 X2
       grind)
    | exact resolve eq15 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq972 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (τ (M.op X0 (M.op X0 X0))) (τ (M.op X0 (M.op X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq902 (τ (M.op X0 (M.op X0 X0))) X1
       have i₂ := eq902 X0 (τ (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq902 eq902
    | exact resolve eq902 eq902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1011 : ∀ X0 X1 : G, (M.op X1 (τ (τ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq972 X0 X1
       have i₂ := eq902 X0 (τ (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq902 eq972
    | exact resolve eq972 eq902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq3004 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq637 y (σ x) X0
       grind)
    | exact superpose eq637 eq16
    | (have j1 := eq637 y x X0
       grind)
    | exact resolve eq16 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3021 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X2 (σ (τ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq637 (τ X1) X2 X0
       grind)
    | exact superpose eq637 eq20
    | (have j1 := eq637 (τ X1) X2 X2
       grind)
    | exact resolve eq20 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq637
  have eq3035 : ∀ X0 X1 X2 : G, (M.op X2 X1) = X2 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3021 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3021
    | (have j0 := eq3021 X0 X1 X2
       grind)
    | exact resolve eq3021 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3021
  have eq43284 : ∀ X0 X1 X2 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X2 (σ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3035 X1 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3035
    | (have j0 := eq3035 X0 (σ X0) X2
       grind)
    | exact resolve eq3035 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3035
  have eq43841 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X2 (σ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43284 X0 X1 X2
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq43284
    | (have j0 := eq43284 X0 X1 X2
       grind)
    | exact resolve eq43284 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43284
  have eq50092 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq947 x y X0
       grind)
    | exact superpose eq947 eq16
    | (have j1 := eq947 X0 y X0
       grind)
    | exact resolve eq16 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq50526 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq50092 X0
       have j1 := eq43841 y x X0
       grind)
    | (have r₁ := eq50092 X0
       have r₂ := eq43841 y x x
       grind)
    | exact resolve eq50092 eq43841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43841 eq50092
  have eq50776 : ∀ X0 : G, (M.op X0 (τ (M.op (σ y) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq902 (σ y) X0
       have i₂ := eq50526 (σ y)
       grind)
    | exact superpose eq50526 eq902
    | exact resolve eq902 eq50526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902
  have eq50778 : ∀ X0 : G, (M.op X0 (τ (τ (M.op (σ y) (σ y))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1011 (σ y) X0
       have i₂ := eq50526 (σ y)
       grind)
    | exact superpose eq50526 eq1011
    | exact resolve eq1011 eq50526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq50826 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq50526 (σ x)
       grind)
    | exact superpose eq50526 eq16
    | exact resolve eq16 eq50526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50874 : ∀ X0 : G, (M.op X0 (τ (τ (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq50778 X0
       have i₂ := eq50526 (σ y)
       grind)
    | exact superpose eq50526 eq50778
    | exact resolve eq50778 eq50526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50778
  have eq50875 : ∀ X0 : G, (M.op X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq50776 X0
       have i₂ := eq50526 (σ y)
       grind)
    | exact superpose eq50526 eq50776
    | exact resolve eq50776 eq50526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50526 eq50776
  have eq50923 : ∀ X0 : G, (M.op X0 (τ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq50874 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq50874
    | exact resolve eq50874 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50874
  have eq50924 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq50875 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq50875
    | exact resolve eq50875 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50875
  have eq51455 : ∀ X0 X1 : G, (k X0 (M.op y y)) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq194 X0 y X1
       have i₂ := eq50924 y
       grind)
    | exact superpose eq50924 eq194
    | (have j0 := eq194 X0 X1 X1
       grind)
    | exact resolve eq194 eq50924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq51528 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq3004 X0
       have i₂ := eq50924 x
       grind)
    | exact superpose eq50924 eq3004
    | (have j0 := eq3004 X0
       grind)
    | exact resolve eq3004 eq50924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3004
  have eq51529 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq51528 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51528
  have eq51536 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq51529 X0
       have i₂ := eq50924 X0
       grind)
    | exact superpose eq50924 eq51529
    | exact resolve eq51529 eq50924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51529
  have eq51585 : ∀ X0 X1 : G, (k X0 y) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51455 X0 X1
       have i₂ := eq50924 y
       grind)
    | exact superpose eq50924 eq51455
    | (have j0 := eq51455 X0 X1
       grind)
    | exact resolve eq51455 eq50924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50924 eq51455
  have eq51608 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51585 X0 X1
       grind)
    | (have r₁ := eq51585 X0 X1
       have r₂ := eq51536 X0
       grind)
    | exact resolve eq51585 eq51536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51536 eq51585
  have eq52500 : ∀ X0 : G, (τ y) ≠ (τ y) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 (τ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (τ y)
       have i₂ := eq50923 (τ y)
       grind)
    | exact superpose eq50923 eq13
    | (have j0 := eq13 X0 (τ y)
       grind)
    | (have r₁ := eq13 X0 (τ y)
       have r₂ := eq50923 (τ y)
       grind)
    | exact resolve eq13 eq50923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52599 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 (τ y)) := by
    intro X0
    first
    | (have j0 := eq52500 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52500
  have eq52654 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (τ y)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52599 X0
       have i₂ := eq51608 X0 (τ y)
       grind)
    | exact superpose eq51608 eq52599
    | (have j0 := eq52599 X0
       grind)
    | exact resolve eq52599 eq51608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51608 eq52599
  have eq52693 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52654 X0
       have i₂ := eq50923 X0
       grind)
    | exact superpose eq50923 eq52654
    | (have j0 := eq52654 X0
       grind)
    | exact resolve eq52654 eq50923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50923 eq52654
  have eq52694 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq52693 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52693
  have eq53628 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq52694 X0
       grind)
    | exact superpose eq52694 eq9
    | exact resolve eq9 eq52694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53805 : ∀ X0 X1 : G, (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53628 X0 X1
       have i₂ := eq52694 X0
       grind)
    | exact superpose eq52694 eq53628
    | exact resolve eq53628 eq52694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52694 eq53628
  have eq57375 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq50826
       have i₂ := eq53805 y x
       grind)
    | exact superpose eq53805 eq50826
    | exact resolve eq50826 eq53805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50826 eq53805
  have eq57376 : False := by grind
  exact eq57376

/-- `Equation56`: `x = x ◇ (y ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_x_pxy_Equation56 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law56 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law56.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X1))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq27 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k X1 (M.op X0 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq9 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X1 (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq13 X0 (M.op X1 (M.op X1 X1))
       have r₂ := eq9 (M.op X1 (M.op X1 X1)) X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X1 (M.op X0 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq34 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq42 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 X2
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq51 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq43 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq43 X0 (M.op X0 X0) X2
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq43 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq52 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq47 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq47 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq47 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq69 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 (M.op X2 (M.op X2 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq28 X2 X0
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq28 X2 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq75 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 (M.op X2 (M.op X2 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq69 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq103 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq51 X0 X0 X2
       grind)
    | exact superpose eq51 eq9
    | (have j1 := eq51 X0 X1 X2
       grind)
    | exact resolve eq9 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq52 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq152 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq151 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq157 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq152 (σ X0)
       grind)
    | exact superpose eq152 eq15
    | exact resolve eq15 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq157 X0
       have i₂ := eq152 X0
       grind)
    | exact superpose eq152 eq157
    | exact resolve eq157 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq199 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq171 X0
       grind)
    | exact superpose eq171 eq9
    | exact resolve eq9 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq199 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq9 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq9 eq199
    | exact resolve eq199 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq380 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq350 X0 X1
       have i₂ := eq171 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq171 eq350
    | exact resolve eq350 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq350
  have eq387 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq380 X0 X1
       have i₂ := eq9 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq9 eq380
    | exact resolve eq380 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq869 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq103 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq103 eq15
    | (have j1 := eq103 (σ X1) X2 X2
       grind)
    | exact resolve eq15 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq871 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq103 X1 X2 (τ X0)
       grind)
    | exact superpose eq103 eq19
    | (have j1 := eq103 X1 X2 X2
       grind)
    | exact resolve eq19 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq103
  have eq2087 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X1))) ≠ X0 ∨ (k X0 (M.op X1 (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq2089 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2087 X0 X1
       grind)
    | (have r₁ := eq2087 X0 X1
       have r₂ := eq9 X0 X1
       grind)
    | exact resolve eq2087 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2087
  have eq2140 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2089 X1 X0
       have i₂ := eq51 X0 X0 X2
       grind)
    | exact superpose eq51 eq2089
    | (have j1 := eq51 X0 X1 X2
       grind)
    | exact resolve eq2089 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq2089
  have eq4240 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2140 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2140
  have eq39449 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq871 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq871
    | (have j0 := eq871 X0 X1 X2
       grind)
    | exact resolve eq871 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq40031 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39449 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq39449
    | (have j0 := eq39449 X0 X1 X2
       grind)
    | exact resolve eq39449 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39449
  have eq43903 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq869 x y X0
       grind)
    | exact superpose eq869 eq16
    | (have j1 := eq869 X0 y X0
       grind)
    | exact resolve eq16 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq69689 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ y)) = X0 ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43903 X0
       have i₂ := eq40031 x y X1
       grind)
    | exact superpose eq40031 eq43903
    | (have j0 := eq43903 X0
       have j1 := eq40031 X0 (σ y) X0
       grind)
    | (have r₁ := eq43903 X0
       have r₂ := eq40031 x y x
       grind)
    | exact resolve eq43903 eq40031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40031 eq43903
  have eq69692 : ∀ X0 X1 : G, (M.op X0 (σ y)) = X0 ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq69689 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69689
  have eq70883 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ y)) = X0 ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4240 X0 (σ y)
       have i₂ := eq69692 X0 X1
       grind)
    | exact superpose eq69692 eq4240
    | (have j0 := eq4240 X0 (σ y)
       have j1 := eq69692 X0 X1
       grind)
    | (have r₁ := eq4240 X0 (σ y)
       have r₂ := eq69692 X0 X1
       grind)
    | (have r₁ := eq4240 X1 y
       have r₂ := eq69692 X0 X1
       grind)
    | exact resolve eq4240 eq69692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4240 eq69692
  have eq70933 : ∀ X0 X1 : G, (k X0 (σ y)) = X0 ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq70883 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70883
  have eq72147 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ y))) ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ y)
       have i₂ := eq70933 (σ X0) X1
       grind)
    | exact superpose eq70933 eq34
    | (have j1 := eq70933 X0 X1
       grind)
    | exact resolve eq34 eq70933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq70933
  have eq72209 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 y) ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72147 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq72147
    | (have j0 := eq72147 X0 X1
       grind)
    | exact resolve eq72147 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72147
  have eq72222 : ∀ X0 X1 : G, (k X0 y) = X0 ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72209 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq72209
    | (have j0 := eq72209 X0 X1
       grind)
    | exact resolve eq72209 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72209
  have eq73129 : ∀ X0 : G, y = (M.op y y) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq152 y
       have i₂ := eq72222 y X0
       grind)
    | exact superpose eq72222 eq152
    | (have j1 := eq72222 X0 y
       grind)
    | exact resolve eq152 eq72222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq72222
  have eq74075 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have j0 := eq73129 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73129
  have eq74076 : y = (M.op y y) := by grind
  clear eq74075
  have eq75208 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq74076
       grind)
    | exact superpose eq74076 eq9
    | exact resolve eq9 eq74076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75245 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq387 y X0
       have i₂ := eq74076
       grind)
    | exact superpose eq74076 eq387
    | exact resolve eq387 eq74076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq75394 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq75245 X0
       have i₂ := eq74076
       grind)
    | exact superpose eq74076 eq75245
    | exact resolve eq75245 eq74076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75245
  have eq75410 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq75208 X0
       have i₂ := eq74076
       grind)
    | exact superpose eq74076 eq75208
    | exact resolve eq75208 eq74076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74076 eq75208
  have eq81962 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq75394 (σ x)
       grind)
    | exact superpose eq75394 eq16
    | exact resolve eq16 eq75394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75394
  have eq81987 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq81962
       have i₂ := eq75410 x
       grind)
    | exact superpose eq75410 eq81962
    | exact resolve eq81962 eq75410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75410 eq81962
  have eq81988 : False := by grind
  exact eq81988

/-- `Equation56`: `x = x ◇ (y ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_pxy_pyx_Equation56 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law56 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law56.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X1))) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq24 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq23
  have eq47 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 X1 (M.op X1 X1)
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq48 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (M.op (σ X1) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq61 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq10
    | (have j1 := eq53 X1 X0
       grind)
    | exact resolve eq10 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq204 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq193 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq193
    | (have j0 := eq193 X0 X1
       grind)
    | exact resolve eq193 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq255 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq9 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq274 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq255 X0 X1
       have i₂ := eq24 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq24 eq255
    | exact resolve eq255 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq281 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq274 X0 X1
       have i₂ := eq9 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq9 eq274
    | exact resolve eq274 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq955 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq1019 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq955 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq955
    | (have j0 := eq955 (M.op X1 X1) X1
       grind)
    | exact resolve eq955 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq1850 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq204 y x
       grind)
    | exact superpose eq204 eq16
    | (have j1 := eq204 y x
       grind)
    | exact resolve eq16 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq20550 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1850
       have i₂ := eq1019 x y
       grind)
    | exact superpose eq1019 eq1850
    | (have j1 := eq1019 (M.op y y) y
       grind)
    | (have r₁ := eq1850
       have r₂ := eq1019 x y
       grind)
    | (have r₁ := eq1850
       have r₂ := eq1019 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1850
       have r₂ := eq1019 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1850 eq1019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019 eq1850
  have eq20551 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20550
  have eq20552 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20551
  have eq20557 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq20552
       grind)
    | exact superpose eq20552 eq9
    | exact resolve eq9 eq20552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20552
  have eq21034 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq20557 y
       grind)
    | exact superpose eq20557 eq9
    | exact resolve eq9 eq20557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21037 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq281 y X0
       have i₂ := eq20557 y
       grind)
    | exact superpose eq20557 eq281
    | exact resolve eq281 eq20557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq20557
  have eq21930 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq21037 (σ x)
       grind)
    | exact superpose eq21037 eq16
    | exact resolve eq16 eq21037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21037
  have eq23965 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq21930
       have i₂ := eq21034 x
       grind)
    | exact superpose eq21034 eq21930
    | exact resolve eq21930 eq21034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21034 eq21930
  have eq23966 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq23965
  have eq23967 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq23966
  have eq24293 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq23967
       grind)
    | exact superpose eq23967 eq10
    | exact resolve eq10 eq23967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23967
  have eq24371 : x = y ∨ x = y := by
    first
    | (have i₁ := eq24293
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq24293
    | exact resolve eq24293 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24293
  have eq24372 : x = y := by grind
  clear eq24371
  have eq24628 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24372
       grind)
    | exact superpose eq24372 eq16
    | exact resolve eq16 eq24372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24372
  have eq24629 : False := by grind
  exact eq24629

/-- `Equation56`: `x = x ◇ (y ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_pyy_pyx_Equation56 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law56 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law56.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X1))) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq24 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq23
  have eq47 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 X1 (M.op X1 X1)
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq48 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (M.op (σ X1) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq61 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq10
    | (have j1 := eq53 X1 X0
       grind)
    | exact resolve eq10 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq247 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq236 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq236
    | (have j0 := eq236 X0 X1
       grind)
    | exact resolve eq236 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq300 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq9 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq325 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq300 X0 X1
       have i₂ := eq24 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq24 eq300
    | exact resolve eq300 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq332 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq325 X0 X1
       have i₂ := eq9 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq9 eq325
    | exact resolve eq325 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq1086 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq1157 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1086 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1086
    | (have j0 := eq1086 (M.op X1 X1) X1
       grind)
    | exact resolve eq1086 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086
  have eq2662 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq247 y x
       grind)
    | exact superpose eq247 eq16
    | (have j1 := eq247 y x
       grind)
    | exact resolve eq16 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq49171 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq2662
       have i₂ := eq1157 x y
       grind)
    | exact superpose eq1157 eq2662
    | (have j1 := eq1157 (M.op y y) y
       grind)
    | (have r₁ := eq2662
       have r₂ := eq1157 x y
       grind)
    | (have r₁ := eq2662
       have r₂ := eq1157 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2662
       have r₂ := eq1157 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2662 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157 eq2662
  have eq49172 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq49171
  have eq49173 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq49172
  have eq49183 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq49173
       grind)
    | exact superpose eq49173 eq9
    | exact resolve eq9 eq49173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49173
  have eq49945 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq49183 y
       grind)
    | exact superpose eq49183 eq9
    | exact resolve eq9 eq49183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49962 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq332 y X0
       have i₂ := eq49183 y
       grind)
    | exact superpose eq49183 eq332
    | exact resolve eq332 eq49183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332 eq49183
  have eq51945 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq49962 (σ x)
       grind)
    | exact superpose eq49962 eq16
    | exact resolve eq16 eq49962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49962
  have eq55263 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq51945
       have i₂ := eq49945 x
       grind)
    | exact superpose eq49945 eq51945
    | exact resolve eq51945 eq49945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49945 eq51945
  have eq55264 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq55263
  have eq55265 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq55264
  have eq55735 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq55265
       grind)
    | exact superpose eq55265 eq10
    | exact resolve eq10 eq55265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55265
  have eq55825 : x = y ∨ x = y := by
    first
    | (have i₁ := eq55735
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq55735
    | exact resolve eq55735 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55735
  have eq55826 : x = y := by grind
  clear eq55825
  have eq56349 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq55826
       grind)
    | exact superpose eq55826 eq16
    | exact resolve eq16 eq55826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55826
  have eq56350 : False := by grind
  exact eq56350

/-- `Equation56`: `x = x ◇ (y ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_x_pyx_Equation56 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law56 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law56.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X1))) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq24 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq23
  have eq47 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 X1 (M.op X1 X1)
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq48 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (M.op (σ X1) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq61 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq10
    | (have j1 := eq53 X1 X0
       grind)
    | exact resolve eq10 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq206 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq195 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq195
    | (have j0 := eq195 X0 X1
       grind)
    | exact resolve eq195 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq257 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq9 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq276 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq257 X0 X1
       have i₂ := eq24 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq24 eq257
    | exact resolve eq257 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq283 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq276 X0 X1
       have i₂ := eq9 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq9 eq276
    | exact resolve eq276 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq956 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq1022 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq956 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq956
    | (have j0 := eq956 (M.op X1 X1) X1
       grind)
    | exact resolve eq956 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq1670 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq206 y x
       grind)
    | exact superpose eq206 eq16
    | (have j1 := eq206 y x
       grind)
    | exact resolve eq16 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq19680 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1670
       have i₂ := eq1022 x y
       grind)
    | exact superpose eq1022 eq1670
    | (have j1 := eq1022 (M.op y y) y
       grind)
    | (have r₁ := eq1670
       have r₂ := eq1022 x y
       grind)
    | (have r₁ := eq1670
       have r₂ := eq1022 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1670
       have r₂ := eq1022 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1670 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022 eq1670
  have eq19681 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19680
  have eq19682 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19681
  have eq19687 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq19682
       grind)
    | exact superpose eq19682 eq9
    | exact resolve eq9 eq19682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19682
  have eq20157 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq19687 y
       grind)
    | exact superpose eq19687 eq9
    | exact resolve eq9 eq19687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20160 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq283 y X0
       have i₂ := eq19687 y
       grind)
    | exact superpose eq19687 eq283
    | exact resolve eq283 eq19687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283 eq19687
  have eq21040 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq20160 (σ x)
       grind)
    | exact superpose eq20160 eq16
    | exact resolve eq16 eq20160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20160
  have eq23118 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq21040
       have i₂ := eq20157 x
       grind)
    | exact superpose eq20157 eq21040
    | exact resolve eq21040 eq20157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20157 eq21040
  have eq23119 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq23118
  have eq23120 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq23119
  have eq23476 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq23120
       grind)
    | exact superpose eq23120 eq10
    | exact resolve eq10 eq23120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23120
  have eq23552 : x = y ∨ x = y := by
    first
    | (have i₁ := eq23476
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23476
    | exact resolve eq23476 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23476
  have eq23553 : x = y := by grind
  clear eq23552
  have eq23835 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23553
       grind)
    | exact superpose eq23553 eq16
    | exact resolve eq16 eq23553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23553
  have eq23836 : False := by grind
  exact eq23836

/-- `Equation56`: `x = x ◇ (y ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_y_pyx_Equation56 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law56 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law56.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X1))) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq24 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq23
  have eq47 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 X1 (M.op X1 X1)
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq48 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (M.op (σ X1) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq61 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq10
    | (have j1 := eq53 X1 X0
       grind)
    | exact resolve eq10 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq202 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq191 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq191
    | (have j0 := eq191 X0 X1
       grind)
    | exact resolve eq191 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq253 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq9 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq272 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq253 X0 X1
       have i₂ := eq24 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq24 eq253
    | exact resolve eq253 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq279 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq272 X0 X1
       have i₂ := eq9 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq9 eq272
    | exact resolve eq272 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq1132 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq1202 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1132 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1132
    | (have j0 := eq1132 (M.op X1 X1) X1
       grind)
    | exact resolve eq1132 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132
  have eq2420 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq202 y x
       grind)
    | exact superpose eq202 eq16
    | (have j1 := eq202 y x
       grind)
    | exact resolve eq16 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq21035 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq2420
       have i₂ := eq1202 x y
       grind)
    | exact superpose eq1202 eq2420
    | (have j1 := eq1202 (M.op y y) y
       grind)
    | (have r₁ := eq2420
       have r₂ := eq1202 x y
       grind)
    | (have r₁ := eq2420
       have r₂ := eq1202 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2420
       have r₂ := eq1202 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2420 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202 eq2420
  have eq21036 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq21035
  have eq21037 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq21036
  have eq21042 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq21037
       grind)
    | exact superpose eq21037 eq9
    | exact resolve eq9 eq21037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21037
  have eq21529 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq21042 y
       grind)
    | exact superpose eq21042 eq9
    | exact resolve eq9 eq21042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21533 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq279 y X0
       have i₂ := eq21042 y
       grind)
    | exact superpose eq21042 eq279
    | exact resolve eq279 eq21042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279 eq21042
  have eq22378 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq21533 (σ x)
       grind)
    | exact superpose eq21533 eq16
    | exact resolve eq16 eq21533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21533
  have eq24571 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq22378
       have i₂ := eq21529 x
       grind)
    | exact superpose eq21529 eq22378
    | exact resolve eq22378 eq21529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21529 eq22378
  have eq24572 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq24571
  have eq24573 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq24572
  have eq24923 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24573
       grind)
    | exact superpose eq24573 eq10
    | exact resolve eq10 eq24573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24573
  have eq25000 : x = y ∨ x = y := by
    first
    | (have i₁ := eq24923
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq24923
    | exact resolve eq24923 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24923
  have eq25001 : x = y := by grind
  clear eq25000
  have eq25384 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25001
       grind)
    | exact superpose eq25001 eq16
    | exact resolve eq16 eq25001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25001
  have eq25385 : False := by grind
  exact eq25385

/-- `Equation56`: `x = x ◇ (y ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation56 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law56 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law56.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq24 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq23
  have eq47 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq83 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq48 x y
       grind)
    | exact superpose eq48 eq16
    | (have j1 := eq48 x y
       grind)
    | exact resolve eq16 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq530 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47
    | exact resolve eq47 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq557 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq530 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq530
    | (have j0 := eq530 X0 X1
       grind)
    | exact resolve eq530 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq1305 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq83
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq83
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq83
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq83
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq83 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq1306 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1305
  have eq13737 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1306
       grind)
    | exact superpose eq1306 eq16
    | exact resolve eq16 eq1306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13738 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq1306
       grind)
    | exact superpose eq1306 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1306
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1306
       grind)
    | exact resolve eq13 eq1306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306
  have eq13739 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq13738
  have eq13740 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq13739
  have eq13742 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13740
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq13740
    | exact resolve eq13740 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13740
  have eq114494 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq557 y x
       have i₂ := eq13742
       grind)
    | exact superpose eq13742 eq557
    | (have j0 := eq557 y x
       grind)
    | exact resolve eq557 eq13742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq114496 : (k x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq13742
       grind)
    | exact superpose eq13742 eq10
    | exact resolve eq10 eq13742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13742
  have eq114612 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq114494
  have eq114650 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq114496
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq114496
    | exact resolve eq114496 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114496
  have eq114651 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq114612
       have r₂ := eq13737
       grind)
    | exact resolve eq114612 eq13737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13737 eq114612
  have eq114654 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq114650
       have r₂ := eq13 x y
       grind)
    | exact resolve eq114650 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114650
  have eq115466 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq85 x y
       have i₂ := eq114654
       grind)
    | exact superpose eq114654 eq85
    | (have j0 := eq85 x y
       grind)
    | exact resolve eq85 eq114654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq114654
  have eq115469 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq115466
  have eq115470 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq115469
  have eq115960 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq115470
       grind)
    | exact superpose eq115470 eq16
    | exact resolve eq16 eq115470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115470
  have eq116376 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq115960
       have i₂ := eq114651
       grind)
    | exact superpose eq114651 eq115960
    | exact resolve eq115960 eq114651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114651 eq115960
  have eq116377 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq116376
  have eq116378 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq116377
  have eq116767 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq116378
       grind)
    | exact superpose eq116378 eq10
    | exact resolve eq10 eq116378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116378
  have eq116927 : x = y ∨ x = y := by
    first
    | (have i₁ := eq116767
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq116767
    | exact resolve eq116767 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116767
  have eq116928 : x = y := by grind
  clear eq116927
  have eq117426 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq116928
       grind)
    | exact superpose eq116928 eq16
    | exact resolve eq16 eq116928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116928
  have eq117427 : False := by grind
  exact eq117427

/-- `Equation56`: `x = x ◇ (y ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pyy_pxy_Equation56 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law56 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law56.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X1))) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq24 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq23
  have eq48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X1) (σ X1)) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq61 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq10
    | (have j1 := eq53 X1 X0
       grind)
    | exact resolve eq10 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq206 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq195 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq195
    | (have j0 := eq195 X0 X1
       grind)
    | exact resolve eq195 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq257 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq9 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq276 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq257 X0 X1
       have i₂ := eq24 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq24 eq257
    | exact resolve eq257 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq283 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq276 X0 X1
       have i₂ := eq9 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq9 eq276
    | exact resolve eq276 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq838 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49
    | (have j0 := eq49 X0 X1
       grind)
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq899 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq838 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq838
    | (have j0 := eq838 (M.op X1 X1) X1
       grind)
    | exact resolve eq838 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq1671 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq206 y x
       grind)
    | exact superpose eq206 eq16
    | (have j1 := eq206 y x
       grind)
    | exact resolve eq16 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq19676 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1671
       have i₂ := eq899 x y
       grind)
    | exact superpose eq899 eq1671
    | (have j1 := eq899 (M.op y y) y
       grind)
    | (have r₁ := eq1671
       have r₂ := eq899 x y
       grind)
    | (have r₁ := eq1671
       have r₂ := eq899 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1671
       have r₂ := eq899 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1671 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899 eq1671
  have eq19677 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19676
  have eq19678 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19677
  have eq19683 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq19678
       grind)
    | exact superpose eq19678 eq9
    | exact resolve eq9 eq19678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19678
  have eq20153 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq19683 y
       grind)
    | exact superpose eq19683 eq9
    | exact resolve eq9 eq19683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20156 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq283 y X0
       have i₂ := eq19683 y
       grind)
    | exact superpose eq19683 eq283
    | exact resolve eq283 eq19683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283 eq19683
  have eq21024 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq20156 (σ x)
       grind)
    | exact superpose eq20156 eq16
    | exact resolve eq16 eq20156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20156
  have eq23101 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq21024
       have i₂ := eq20153 x
       grind)
    | exact superpose eq20153 eq21024
    | exact resolve eq21024 eq20153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20153 eq21024
  have eq23102 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq23101
  have eq23103 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq23102
  have eq23401 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq23103
       grind)
    | exact superpose eq23103 eq10
    | exact resolve eq10 eq23103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23103
  have eq23478 : x = y ∨ x = y := by
    first
    | (have i₁ := eq23401
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23401
    | exact resolve eq23401 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23401
  have eq23479 : x = y := by grind
  clear eq23478
  have eq23761 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23479
       grind)
    | exact superpose eq23479 eq16
    | exact resolve eq16 eq23479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23479
  have eq23762 : False := by grind
  exact eq23762

/-- `Equation56`: `x = x ◇ (y ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxy_pxx_pxy_Equation56 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law56 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law56.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X1))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq24 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq23
  have eq48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X1) (σ X1)) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq61 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq10
    | (have j1 := eq53 X1 X0
       grind)
    | exact resolve eq10 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq247 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq236 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq236
    | (have j0 := eq236 X0 X1
       grind)
    | exact resolve eq236 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq300 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq9 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq325 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq300 X0 X1
       have i₂ := eq24 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq24 eq300
    | exact resolve eq300 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq332 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq325 X0 X1
       have i₂ := eq9 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq9 eq325
    | exact resolve eq325 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq1086 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49
    | (have j0 := eq49 X0 X1
       grind)
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1157 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1086 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1086
    | (have j0 := eq1086 (M.op X1 X1) X1
       grind)
    | exact resolve eq1086 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086
  have eq2662 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq247 y x
       grind)
    | exact superpose eq247 eq16
    | (have j1 := eq247 y x
       grind)
    | exact resolve eq16 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq49169 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq2662
       have i₂ := eq1157 x y
       grind)
    | exact superpose eq1157 eq2662
    | (have j1 := eq1157 (M.op y y) y
       grind)
    | (have r₁ := eq2662
       have r₂ := eq1157 x y
       grind)
    | (have r₁ := eq2662
       have r₂ := eq1157 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2662
       have r₂ := eq1157 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2662 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157 eq2662
  have eq49170 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq49169
  have eq49171 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq49170
  have eq49180 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq49171
       grind)
    | exact superpose eq49171 eq9
    | exact resolve eq9 eq49171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49171
  have eq49942 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq49180 y
       grind)
    | exact superpose eq49180 eq9
    | exact resolve eq9 eq49180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49959 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq332 y X0
       have i₂ := eq49180 y
       grind)
    | exact superpose eq49180 eq332
    | exact resolve eq332 eq49180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332 eq49180
  have eq51942 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq49959 (σ x)
       grind)
    | exact superpose eq49959 eq16
    | exact resolve eq16 eq49959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49959
  have eq55264 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq51942
       have i₂ := eq49942 x
       grind)
    | exact superpose eq49942 eq51942
    | exact resolve eq51942 eq49942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49942 eq51942
  have eq55265 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq55264
  have eq55266 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq55265
  have eq55803 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq55266
       grind)
    | exact superpose eq55266 eq10
    | exact resolve eq10 eq55266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55266
  have eq55894 : x = y ∨ x = y := by
    first
    | (have i₁ := eq55803
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq55803
    | exact resolve eq55803 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55803
  have eq55895 : x = y := by grind
  clear eq55894
  have eq56388 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq55895
       grind)
    | exact superpose eq55895 eq16
    | exact resolve eq16 eq55895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55895
  have eq56389 : False := by grind
  exact eq56389

/-- `Equation614`: `x = x ◇ (x ◇ ((x ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_x_pxx_x_pxy_Equation614 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law614 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law614.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq109 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq12
    | exact resolve eq12 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq190 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq184 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq184 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq184 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq237 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq190 (σ X0) (σ X1)
       grind)
    | exact superpose eq190 eq15
    | (have j1 := eq190 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq190 X0 (τ X1)
       grind)
    | exact superpose eq190 eq18
    | (have j1 := eq190 X0 (τ X1)
       grind)
    | exact resolve eq18 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq190
  have eq1685 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq243 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq243
    | exact resolve eq243 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq1750 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1685 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1685
    | (have j0 := eq1685 X0 X1
       grind)
    | exact resolve eq1685 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1685
  have eq2964 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq237 x y
       grind)
    | exact superpose eq237 eq16
    | (have j1 := eq237 x y
       grind)
    | exact resolve eq16 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2997 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq237 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq4672 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2964
       have i₂ := eq1750 y x
       grind)
    | exact superpose eq1750 eq2964
    | (have j1 := eq1750 (σ y) (σ x)
       grind)
    | (have r₁ := eq2964
       have r₂ := eq1750 y x
       grind)
    | exact resolve eq2964 eq1750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2964
  have eq4673 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4672
  have eq5005 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4673
       grind)
    | exact superpose eq4673 eq16
    | exact resolve eq16 eq4673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5008 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq4673
       grind)
    | exact superpose eq4673 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq4673
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq4673
       grind)
    | exact resolve eq13 eq4673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5011 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq5008
  have eq5014 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5011
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq5011
    | exact resolve eq5011 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq5011
  have eq5020 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5014
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq5014
    | exact resolve eq5014 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5014
  have eq14038 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1750 y x
       have i₂ := eq5020
       grind)
    | exact superpose eq5020 eq1750
    | (have j0 := eq1750 y x
       grind)
    | exact resolve eq1750 eq5020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5020
  have eq14096 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq14038
  have eq14131 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14096
       have r₂ := eq5005
       grind)
    | exact resolve eq14096 eq5005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14096
  have eq14256 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq14131
       grind)
    | exact superpose eq14131 eq10
    | exact resolve eq10 eq14131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14131
  have eq14324 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14256
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq14256
    | exact resolve eq14256 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14256
  have eq14558 : x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq14324
       grind)
    | exact superpose eq14324 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq14324
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq14324
       grind)
    | exact resolve eq13 eq14324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14560 : x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) := by grind
  clear eq14558
  have eq14561 : x = (k x y) ∨ x = (M.op x x) := by grind
  clear eq14560
  have eq14860 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2997 x y
       have i₂ := eq14561
       grind)
    | exact superpose eq14561 eq2997
    | (have j0 := eq2997 x y
       grind)
    | exact resolve eq2997 eq14561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14561
  have eq14871 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq14860
  have eq15322 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14871
       grind)
    | exact superpose eq14871 eq16
    | exact resolve eq16 eq14871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14871
  have eq15373 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15322
       have i₂ := eq14324
       grind)
    | exact superpose eq14324 eq15322
    | exact resolve eq15322 eq14324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14324 eq15322
  have eq15374 : (σ x) ≠ (σ x) ∨ x = (M.op x x) := by grind
  clear eq15373
  have eq15375 : x = (M.op x x) := by grind
  clear eq15374
  have eq15481 : ∀ X0 : G, x ≠ (M.op x X0) ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x x
       have i₂ := eq15375
       grind)
    | exact superpose eq15375 eq12
    | exact resolve eq12 eq15375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15484 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (σ x) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq109 x x
       have i₂ := eq15375
       grind)
    | exact superpose eq15375 eq109
    | exact resolve eq109 eq15375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq15375
  have eq16342 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15484 (σ y)
       have i₂ := eq4673
       grind)
    | exact superpose eq4673 eq15484
    | (have j0 := eq15484 (σ y)
       grind)
    | (have r₁ := eq15484 (σ y)
       have r₂ := eq4673
       grind)
    | exact resolve eq15484 eq4673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4673 eq15484
  have eq16365 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16342
  have eq16376 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16365
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq16365
    | exact resolve eq16365 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16365
  have eq16662 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1750 y x
       have i₂ := eq16376
       grind)
    | exact superpose eq16376 eq1750
    | (have j0 := eq1750 y x
       grind)
    | exact resolve eq1750 eq16376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750
  have eq16666 : (k x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq16376
       grind)
    | exact superpose eq16376 eq10
    | exact resolve eq10 eq16376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16376
  have eq16727 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq16662
  have eq16761 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16666
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16666
    | exact resolve eq16666 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16666
  have eq16762 : x = (M.op x y) := by
    first
    | (have r₁ := eq16727
       have r₂ := eq5005
       grind)
    | exact resolve eq16727 eq5005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5005 eq16727
  have eq16772 : x = (k x y) := by
    first
    | (have j1 := eq15481 y
       grind)
    | (have r₁ := eq16761
       have r₂ := eq15481 y
       grind)
    | exact resolve eq16761 eq15481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15481 eq16761
  have eq17365 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2997 x y
       have i₂ := eq16772
       grind)
    | exact superpose eq16772 eq2997
    | (have j0 := eq2997 x y
       grind)
    | exact resolve eq2997 eq16772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2997 eq16772
  have eq17376 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17365
  have eq17770 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17376
       grind)
    | exact superpose eq17376 eq16
    | exact resolve eq16 eq17376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17376
  have eq17786 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq17770
       have i₂ := eq16762
       grind)
    | exact superpose eq16762 eq17770
    | exact resolve eq17770 eq16762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16762 eq17770
  have eq17787 : False := by grind
  exact eq17787

/-- `Equation614`: `x = x ◇ (x ◇ ((x ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_y_pxx_y_pxy_Equation614 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law614 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law614.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq98 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq12
    | exact resolve eq12 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq148 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq145 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq145 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq145 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq145 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq145 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq231 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq148 (σ X0) (σ X1)
       grind)
    | exact superpose eq148 eq15
    | (have j1 := eq148 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq148 (τ X0) X1
       grind)
    | exact superpose eq148 eq17
    | (have j1 := eq148 (τ X0) X1
       grind)
    | exact resolve eq17 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq148
  have eq1555 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq233 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq233
    | exact resolve eq233 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq1633 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1555 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1555
    | (have j0 := eq1555 X0 X1
       grind)
    | exact resolve eq1555 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555
  have eq2557 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq231 x y
       grind)
    | exact superpose eq231 eq16
    | (have j1 := eq231 x y
       grind)
    | exact resolve eq16 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2591 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq231 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq3602 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2557
       have i₂ := eq1633 x y
       grind)
    | exact superpose eq1633 eq2557
    | (have j1 := eq1633 (σ x) (σ y)
       grind)
    | (have r₁ := eq2557
       have r₂ := eq1633 x y
       grind)
    | exact resolve eq2557 eq1633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2557
  have eq3603 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3602
  have eq3917 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3603
       grind)
    | exact superpose eq3603 eq16
    | exact resolve eq16 eq3603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3920 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq3603
       grind)
    | exact superpose eq3603 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3603
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq3603
       grind)
    | exact resolve eq13 eq3603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3924 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3920
  have eq3925 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3924
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq3924
    | exact resolve eq3924 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq3924
  have eq3930 : (σ y) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3925
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3925
    | exact resolve eq3925 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3925
  have eq11760 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1633 x y
       have i₂ := eq3930
       grind)
    | exact superpose eq3930 eq1633
    | (have j0 := eq1633 x y
       grind)
    | exact resolve eq1633 eq3930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3930
  have eq11812 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq11760
  have eq11843 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11812
       have r₂ := eq3917
       grind)
    | exact resolve eq11812 eq3917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11812
  have eq12136 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq11843
       grind)
    | exact superpose eq11843 eq10
    | exact resolve eq10 eq11843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11843
  have eq12198 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12136
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq12136
    | exact resolve eq12136 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12136
  have eq12635 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq12198
       grind)
    | exact superpose eq12198 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq12198
       grind)
    | exact resolve eq13 eq12198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12638 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) := by grind
  clear eq12635
  have eq12639 : y = (k x y) ∨ y = (M.op x x) := by grind
  clear eq12638
  have eq12772 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2591 x y
       have i₂ := eq12639
       grind)
    | exact superpose eq12639 eq2591
    | (have j0 := eq2591 x y
       grind)
    | exact resolve eq2591 eq12639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12639
  have eq12783 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq12772
  have eq13325 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12783
       grind)
    | exact superpose eq12783 eq16
    | exact resolve eq16 eq12783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12783
  have eq13425 : (σ y) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13325
       have i₂ := eq12198
       grind)
    | exact superpose eq12198 eq13325
    | exact resolve eq13325 eq12198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12198 eq13325
  have eq13426 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq13425
  have eq13427 : y = (M.op x x) := by grind
  clear eq13426
  have eq13547 : ∀ X0 : G, y ≠ (M.op x X0) ∨ y = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x x
       have i₂ := eq13427
       grind)
    | exact superpose eq13427 eq12
    | exact resolve eq12 eq13427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13553 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) X0) ∨ (σ y) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq98 x x
       have i₂ := eq13427
       grind)
    | exact superpose eq13427 eq98
    | exact resolve eq98 eq13427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq13427
  have eq14761 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13553 (σ y)
       have i₂ := eq3603
       grind)
    | exact superpose eq3603 eq13553
    | (have j0 := eq13553 (σ y)
       grind)
    | (have r₁ := eq13553 (σ y)
       have r₂ := eq3603
       grind)
    | exact resolve eq13553 eq3603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3603 eq13553
  have eq14776 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14761
  have eq14785 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14776
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq14776
    | exact resolve eq14776 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14776
  have eq15030 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1633 x y
       have i₂ := eq14785
       grind)
    | exact superpose eq14785 eq1633
    | (have j0 := eq1633 x y
       grind)
    | exact resolve eq1633 eq14785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1633
  have eq15035 : (k x y) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq14785
       grind)
    | exact superpose eq14785 eq10
    | exact resolve eq10 eq14785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14785
  have eq15096 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq15030
  have eq15130 : y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15035
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq15035
    | exact resolve eq15035 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15035
  have eq15131 : y = (M.op x y) := by
    first
    | (have r₁ := eq15096
       have r₂ := eq3917
       grind)
    | exact resolve eq15096 eq3917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3917 eq15096
  have eq15140 : y = (k x y) := by
    first
    | (have j1 := eq13547 y
       grind)
    | (have r₁ := eq15130
       have r₂ := eq13547 y
       grind)
    | exact resolve eq15130 eq13547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13547 eq15130
  have eq15896 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2591 x y
       have i₂ := eq15140
       grind)
    | exact superpose eq15140 eq2591
    | (have j0 := eq2591 x y
       grind)
    | exact resolve eq2591 eq15140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2591 eq15140
  have eq15907 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15896
  have eq16535 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15907
       grind)
    | exact superpose eq15907 eq16
    | exact resolve eq16 eq15907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15907
  have eq16550 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq16535
       have i₂ := eq15131
       grind)
    | exact superpose eq15131 eq16535
    | exact resolve eq16535 eq15131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15131 eq16535
  have eq16551 : False := by grind
  exact eq16551
