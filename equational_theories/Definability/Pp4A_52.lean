import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pxy_pxy_pxx_pxy_Equation419 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq56 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq61
    | exact resolve eq61 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq64
    | exact resolve eq64 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq64
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq440 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq92 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq468 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq440 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq440
    | (have j0 := eq440 X0 X1
       grind)
    | exact resolve eq440 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq440
  have eq473 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq468 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq468 X0 (M.op (τ X0) (τ X0))
       have r₂ := eq12 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | (have r₁ := eq468 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq468 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq476 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq473 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq473
    | (have j0 := eq473 X0 X1
       grind)
    | exact resolve eq473 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq473
  have eq568 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq476 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq476
    | exact resolve eq476 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq476 (σ X0) X1
       grind)
    | exact superpose eq476 eq15
    | (have j1 := eq476 (σ X0) X1
       grind)
    | exact resolve eq15 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq599 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq580 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq580
    | (have j0 := eq580 X0 X1
       grind)
    | exact resolve eq580 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq617 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
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
  have eq810 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq617 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq617
    | exact resolve eq617 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq850 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq810 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq810
    | (have j0 := eq810 X0 X1
       grind)
    | exact resolve eq810 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq3342 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq599 x y
       grind)
    | exact superpose eq599 eq16
    | (have j1 := eq599 x y
       grind)
    | exact resolve eq16 eq599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3371 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq599 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq3411 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3342
       have i₂ := eq850 y x
       grind)
    | exact superpose eq850 eq3342
    | (have j1 := eq850 y x
       grind)
    | (have r₁ := eq3342
       have r₂ := eq850 y x
       grind)
    | exact resolve eq3342 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3342
  have eq3412 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3411
  have eq3523 : y ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq3412
       grind)
    | exact superpose eq3412 eq12
    | exact resolve eq12 eq3412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3524 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq3412
       grind)
    | exact superpose eq3412 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq3412
       grind)
    | exact resolve eq13 eq3412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3412
  have eq3534 : (k x y) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3524
  have eq3535 : (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq3523
       have r₂ := eq3534
       grind)
    | exact resolve eq3523 eq3534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3523 eq3534
  have eq3541 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq459 x y
       have i₂ := eq3535
       grind)
    | exact superpose eq3535 eq459
    | (have j0 := eq459 x y
       grind)
    | exact resolve eq459 eq3535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq3551 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3541
  have eq3552 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3551
  have eq3604 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq3552
       grind)
    | exact superpose eq3552 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq3552
       grind)
    | exact resolve eq12 eq3552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3552
  have eq3616 : (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3604
  have eq3622 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq3616
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3616
    | exact resolve eq3616 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3616
  have eq4012 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq3622
       grind)
    | exact superpose eq3622 eq12
    | exact resolve eq12 eq3622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4013 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq3622
       grind)
    | exact superpose eq3622 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq3622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3622
  have eq4031 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq4013
       have r₂ := eq67 x
       grind)
    | exact resolve eq4013 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4013
  have eq4032 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq4012
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq4012
    | exact resolve eq4012 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4012
  have eq4036 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq4031
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq4031
    | exact resolve eq4031 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4031
  have eq4037 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq4036
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq4036
    | exact resolve eq4036 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4036
  have eq4038 : (σ y) = (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4037
       have r₂ := eq4032
       grind)
    | exact resolve eq4037 eq4032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4032 eq4037
  have eq4127 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq4038
  have eq4391 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3371 x y
       have i₂ := eq3535
       grind)
    | exact superpose eq3535 eq3371
    | (have j0 := eq3371 x y
       grind)
    | exact resolve eq3371 eq3535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3371 eq3535
  have eq4419 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq4391
  have eq4420 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq4419
  have eq4505 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4420
       grind)
    | exact superpose eq4420 eq16
    | exact resolve eq16 eq4420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4509 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq4420
       grind)
    | exact superpose eq4420 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq4420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4420
  have eq4530 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4509
       have r₂ := eq67 x
       grind)
    | exact resolve eq4509 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4509
  have eq4535 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4530
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq4530
    | exact resolve eq4530 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4530
  have eq4536 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4535
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq4535
    | exact resolve eq4535 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq4535
  have eq4537 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4536
       have r₂ := eq4127
       grind)
    | exact resolve eq4536 eq4127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4127 eq4536
  have eq4599 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq850 y x
       have i₂ := eq4537
       grind)
    | exact superpose eq4537 eq850
    | (have j0 := eq850 y x
       grind)
    | exact resolve eq850 eq4537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850 eq4537
  have eq4655 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq4599
       have r₂ := eq4505
       grind)
    | exact resolve eq4599 eq4505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4599
  have eq4755 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4505
       have i₂ := eq4655
       grind)
    | exact superpose eq4655 eq4505
    | exact resolve eq4505 eq4655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4505 eq4655
  have eq4778 : False := by grind
  exact eq4778

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pyx_pyx_pxx_pyx_Equation419 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq22 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq22 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
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
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq31 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq34 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq34 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq43 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq36 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq39
    | (have j0 := eq39 X0 X1
       grind)
    | exact resolve eq39 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq40
    | (have j0 := eq40 X0 X1
       grind)
    | exact resolve eq40 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq40
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq45 X0 X1
       grind)
    | (have r₁ := eq46 X0 X1
       have r₂ := eq45 X0 X1
       grind)
    | exact resolve eq46 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq46
  have eq89 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq93 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq89 X0 X1
       have j1 := eq48 X1 X0
       grind)
    | (have r₁ := eq89 X1 X0
       have r₂ := eq48 X0 X1
       grind)
    | (have r₁ := eq89 X0 X0
       have r₂ := eq48 X0 X0
       grind)
    | exact resolve eq89 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq89
  have eq221 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq93 (σ X1) (σ X0)
       grind)
    | exact superpose eq93 eq15
    | exact resolve eq15 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq221 X0 X1
       have i₂ := eq93 X1 X0
       grind)
    | exact superpose eq93 eq221
    | exact resolve eq221 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq221
  have eq230 : False := by grind
  exact eq230

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_pyy_pyx_pyy_pyx_Equation419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq56 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq61
    | exact resolve eq61 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq64
    | exact resolve eq64 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq64
  have eq86 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq92 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq441 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq92 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq469 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq441 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq441
    | (have j0 := eq441 X0 X1
       grind)
    | exact resolve eq441 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq441
  have eq474 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq469 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq469 X1 (M.op (τ X1) (τ X1))
       have r₂ := eq12 (σ (M.op (τ X1) (τ X1))) X1
       grind)
    | (have r₁ := eq469 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq469 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq477 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq474 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq474
    | (have j0 := eq474 X0 X1
       grind)
    | exact resolve eq474 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq474
  have eq568 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq477 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq477
    | exact resolve eq477 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq477 (σ X0) X1
       grind)
    | exact superpose eq477 eq15
    | (have j1 := eq477 (σ X0) X1
       grind)
    | exact resolve eq15 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq599 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq575 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq575
    | (have j0 := eq575 X0 X1
       grind)
    | exact resolve eq575 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq628 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq568 (τ X1) X0
       grind)
    | exact superpose eq568 eq17
    | (have j1 := eq568 (τ X1) X0
       grind)
    | exact resolve eq17 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq568
  have eq810 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq628 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq628
    | exact resolve eq628 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq850 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq810 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq810
    | (have j0 := eq810 X0 X1
       grind)
    | exact resolve eq810 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq3342 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq599 x y
       grind)
    | exact superpose eq599 eq16
    | (have j1 := eq599 x y
       grind)
    | exact resolve eq16 eq599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3371 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq599 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq3411 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3342
       have i₂ := eq850 y x
       grind)
    | exact superpose eq850 eq3342
    | (have j1 := eq850 y x
       grind)
    | (have r₁ := eq3342
       have r₂ := eq850 y x
       grind)
    | exact resolve eq3342 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3342
  have eq3412 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3411
  have eq3523 : y ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq3412
       grind)
    | exact superpose eq3412 eq12
    | exact resolve eq12 eq3412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3524 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq3412
       grind)
    | exact superpose eq3412 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3412
       grind)
    | exact resolve eq13 eq3412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3412
  have eq3534 : (k y x) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3524
  have eq3535 : (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq3523
       have r₂ := eq3534
       grind)
    | exact resolve eq3523 eq3534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3523 eq3534
  have eq3541 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq460 x y
       have i₂ := eq3535
       grind)
    | exact superpose eq3535 eq460
    | (have j0 := eq460 x y
       grind)
    | exact resolve eq460 eq3535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq3551 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3541
  have eq3552 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3551
  have eq3604 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq3552
       grind)
    | exact superpose eq3552 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq3552
       grind)
    | exact resolve eq12 eq3552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3552
  have eq3616 : (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3604
  have eq3622 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq3616
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3616
    | exact resolve eq3616 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3616
  have eq4012 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq3622
       grind)
    | exact superpose eq3622 eq12
    | exact resolve eq12 eq3622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4013 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq3622
       grind)
    | exact superpose eq3622 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq3622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3622
  have eq4031 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq4013
       have r₂ := eq67 x
       grind)
    | exact resolve eq4013 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4013
  have eq4032 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq4012
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4012
    | exact resolve eq4012 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4012
  have eq4036 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq4031
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4031
    | exact resolve eq4031 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4031
  have eq4037 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq4036
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq4036
    | exact resolve eq4036 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4036
  have eq4038 : (σ y) = (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4037
       have r₂ := eq4032
       grind)
    | exact resolve eq4037 eq4032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4032 eq4037
  have eq4127 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq4038
  have eq4391 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3371 x y
       have i₂ := eq3535
       grind)
    | exact superpose eq3535 eq3371
    | (have j0 := eq3371 x y
       grind)
    | exact resolve eq3371 eq3535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3371 eq3535
  have eq4419 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq4391
  have eq4420 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq4419
  have eq4505 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4420
       grind)
    | exact superpose eq4420 eq16
    | exact resolve eq16 eq4420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4509 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq4420
       grind)
    | exact superpose eq4420 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq4420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4420
  have eq4530 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4509
       have r₂ := eq67 x
       grind)
    | exact resolve eq4509 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4509
  have eq4535 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4530
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4530
    | exact resolve eq4530 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4530
  have eq4536 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4535
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq4535
    | exact resolve eq4535 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq4535
  have eq4537 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4536
       have r₂ := eq4127
       grind)
    | exact resolve eq4536 eq4127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4127 eq4536
  have eq4599 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq850 y x
       have i₂ := eq4537
       grind)
    | exact superpose eq4537 eq850
    | (have j0 := eq850 y x
       grind)
    | exact resolve eq850 eq4537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850 eq4537
  have eq4655 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq4599
       have r₂ := eq4505
       grind)
    | exact resolve eq4599 eq4505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4599
  have eq4755 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4505
       have i₂ := eq4655
       grind)
    | exact superpose eq4655 eq4505
    | exact resolve eq4505 eq4655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4505 eq4655
  have eq4778 : False := by grind
  exact eq4778

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyx_pxx_pyx_Equation419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X1 X0)))) = X0 := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq74 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq138 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 (σ X0) (M.op (σ X0) X1)
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq480 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq9
    | (have j1 := eq74 X0
       grind)
    | exact resolve eq9 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq487 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq480 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq480 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq480 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq502 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq487 (σ X0)
       grind)
    | exact superpose eq487 eq15
    | exact resolve eq15 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq502 X0
       have i₂ := eq487 X0
       grind)
    | exact superpose eq487 eq502
    | exact resolve eq502 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487 eq502
  have eq3918 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq141 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq7494 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k X1 (σ X0)) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq138 X0 X1
       grind)
    | exact superpose eq138 eq12
    | (have j1 := eq138 X0 X1
       grind)
    | (have r₁ := eq12 X1 (σ X0)
       have r₂ := eq138 X0 X1
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq138 X0 (M.op (σ X0) X0)
       grind)
    | exact resolve eq12 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq7525 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ X0)) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq7494 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7494
  have eq8589 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ X0 = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7525 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7525
    | exact resolve eq7525 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8617 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq7525 X0 X1
       grind)
    | exact superpose eq7525 eq23
    | (have j1 := eq7525 X0 X1
       grind)
    | exact resolve eq23 eq7525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq7525
  have eq8696 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8617 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8617
    | (have j0 := eq8617 X0 X1
       grind)
    | exact resolve eq8617 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8617
  have eq8702 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8589 X0 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq8589
    | (have j0 := eq8589 X0 X1
       grind)
    | exact resolve eq8589 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8589
  have eq8812 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq8702 X0 X1
       grind)
    | exact superpose eq8702 eq11
    | (have j1 := eq8702 X0 X1
       grind)
    | exact resolve eq11 eq8702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8702
  have eq8937 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8812 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq8812
    | (have j0 := eq8812 X0 X1
       grind)
    | exact resolve eq8812 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8812
  have eq9017 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq8937 X0 (τ X1)
       grind)
    | exact superpose eq8937 eq18
    | (have j1 := eq8937 X0 (τ X1)
       grind)
    | exact resolve eq18 eq8937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq8937
  have eq9155 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (σ (τ X1)) = X0 ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8696 (τ X0) X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq8696
    | (have j0 := eq8696 (τ X1) X0
       grind)
    | exact resolve eq8696 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq8696
  have eq9285 : ∀ X0 X1 : G, X0 = X1 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9155 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq9155
    | (have j0 := eq9155 X0 X1
       grind)
    | exact resolve eq9155 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9155
  have eq9325 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9285 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq9285
    | (have j0 := eq9285 X0 X1
       grind)
    | exact resolve eq9285 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9285
  have eq9463 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq9325 X1 X0
       grind)
    | exact superpose eq9325 eq11
    | (have j1 := eq9325 (k X1 X0) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq9325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9325
  have eq9590 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9463 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq9463
    | (have j0 := eq9463 X0 X1
       grind)
    | exact resolve eq9463 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9463
  have eq9660 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9590 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9590
    | (have j0 := eq9590 (τ (σ (k X0 X1))) (τ (σ X1))
       grind)
    | exact resolve eq9590 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9590
  have eq9838 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = X1 ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9660 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq9660
    | (have j0 := eq9660 X0 X1
       grind)
    | exact resolve eq9660 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9660
  have eq9844 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9838 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq9838
    | (have j0 := eq9838 X0 X1
       grind)
    | exact resolve eq9838 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9838
  have eq10420 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9017 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9017
    | exact resolve eq9017 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9017
  have eq10502 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10420 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10420
    | (have j0 := eq10420 X0 X1
       grind)
    | exact resolve eq10420 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10420
  have eq10801 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9844 y x
       grind)
    | exact superpose eq9844 eq16
    | (have j1 := eq9844 x y
       grind)
    | exact resolve eq16 eq9844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9844
  have eq10853 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10801
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq10801
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq10801
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq10801
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq10801 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10854 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq10801
       have i₂ := eq10502 y x
       grind)
    | exact superpose eq10502 eq10801
    | (have j1 := eq10502 y x
       grind)
    | (have r₁ := eq10801
       have r₂ := eq10502 y x
       grind)
    | (have r₁ := eq10801
       have r₂ := eq10502 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq10801
       have r₂ := eq10502 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq10801 eq10502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10502 eq10801
  have eq10857 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y := by grind
  clear eq10854
  have eq10858 : x = y ∨ x = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq10857
  have eq10859 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq10853
  have eq10860 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq10859
  have eq10863 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10858
       grind)
    | exact superpose eq10858 eq16
    | exact resolve eq16 eq10858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10858
  have eq10864 : x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10863
       have r₂ := eq521 x
       grind)
    | exact resolve eq10863 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10863
  have eq10873 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3918 x y
       have i₂ := eq10864
       grind)
    | exact superpose eq10864 eq3918
    | (have j0 := eq3918 x y
       grind)
    | exact resolve eq3918 eq10864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3918 eq10864
  have eq10879 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10873
  have eq10880 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq10879
  have eq10884 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10860
       grind)
    | exact superpose eq10860 eq16
    | exact resolve eq16 eq10860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10860
  have eq10885 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10884
       have r₂ := eq521 x
       grind)
    | exact resolve eq10884 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10884
  have eq10901 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10880
       grind)
    | exact superpose eq10880 eq16
    | exact resolve eq16 eq10880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10880
  have eq10940 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10901
       have i₂ := eq10885
       grind)
    | exact superpose eq10885 eq10901
    | exact resolve eq10901 eq10885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10885 eq10901
  have eq10945 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq10940
  have eq10946 : (σ x) = (σ y) := by grind
  clear eq10945
  have eq10947 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10946
       grind)
    | exact superpose eq10946 eq16
    | exact resolve eq16 eq10946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10948 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq10946
       grind)
    | exact superpose eq10946 eq10
    | exact resolve eq10 eq10946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10946
  have eq11012 : x = y := by
    first
    | (have i₁ := eq10948
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10948
    | exact resolve eq10948 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10948
  have eq11013 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq10947
       have i₂ := eq521 x
       grind)
    | exact superpose eq521 eq10947
    | exact resolve eq10947 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521 eq10947
  have eq11016 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq11013
       have i₂ := eq11012
       grind)
    | exact superpose eq11012 eq11013
    | exact resolve eq11013 eq11012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11012 eq11013
  have eq11017 : False := by grind
  exact eq11017

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq277 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq83 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq83 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq83 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq289 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq277 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq290 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq289 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq292 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq290 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq290
    | (have j0 := eq290 X0 X1
       grind)
    | exact resolve eq290 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq295 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq292 X0 X1
       have j1 := eq286 X1 X0
       grind)
    | (have r₁ := eq292 X1 X0
       have r₂ := eq286 X0 X1
       grind)
    | (have r₁ := eq292 X1 (k X0 X1)
       have r₂ := eq286 X0 X1
       grind)
    | (have r₁ := eq292 X1 X1
       have r₂ := eq286 X1 X1
       grind)
    | exact resolve eq292 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286 eq292
  have eq534 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq295 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq295
    | exact resolve eq295 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq295 y x
       grind)
    | exact superpose eq295 eq16
    | (have j1 := eq295 y x
       grind)
    | exact resolve eq16 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq556 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq534 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq534
    | (have j0 := eq534 X0 X1
       grind)
    | exact resolve eq534 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq534
  have eq558 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq556 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq556
    | exact resolve eq556 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq617 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq558 (τ X0) X1
       grind)
    | exact superpose eq558 eq18
    | (have j1 := eq558 (τ X0) X1
       grind)
    | exact resolve eq18 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq558
  have eq829 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq617 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq617
    | exact resolve eq617 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq878 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq829 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq829
    | (have j0 := eq829 X0 X1
       grind)
    | exact resolve eq829 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq976 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq542
       have i₂ := eq878 x y
       grind)
    | exact superpose eq878 eq542
    | (have j1 := eq878 (σ x) (σ y)
       grind)
    | (have r₁ := eq542
       have r₂ := eq878 x y
       grind)
    | exact resolve eq542 eq878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq977 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq976
  have eq983 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq977
  have eq1030 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq542
       have i₂ := eq983
       grind)
    | exact superpose eq983 eq542
    | exact resolve eq542 eq983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542 eq983
  have eq1031 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1030
  have eq1032 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1031
  have eq1045 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1032
  have eq1053 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1045
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1045
    | exact resolve eq1045 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1085 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1053
       grind)
    | exact superpose eq1053 eq16
    | exact resolve eq16 eq1053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053
  have eq1097 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1085
       have i₂ := eq878 x y
       grind)
    | exact superpose eq878 eq1085
    | (have j1 := eq878 x y
       grind)
    | (have r₁ := eq1085
       have r₂ := eq878 x y
       grind)
    | exact resolve eq1085 eq878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq1098 : x = (M.op y y) := by grind
  clear eq1097
  have eq1140 : (M.op x y) = (k x y) := by grind
  clear eq1098
  have eq1148 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1085
       have i₂ := eq1140
       grind)
    | exact superpose eq1140 eq1085
    | exact resolve eq1085 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085 eq1140
  have eq1151 : False := by grind
  exact eq1151

/-- `Equation4209`: `x ◇ y = ((z ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_pxx_pyy_pyx_Equation4209 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4209 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4209.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
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
  clear eq17
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
  clear eq22
  have eq52 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
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
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X1 X0)
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq12
    | (have j0 := eq12 X1 (M.op X1 X0)
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq52 X1 X1
       grind)
    | exact resolve eq12 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq101 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq101 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq101 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq106 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
  have eq112 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq102 (τ X0)
       grind)
    | exact superpose eq102 eq18
    | exact resolve eq18 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq112 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq112
    | exact resolve eq112 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq121 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq106 X0
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq106
    | exact resolve eq106 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq125 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq115 X0
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq115
    | exact resolve eq115 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq115
  have eq138 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq52 (σ X0) (σ X0)
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq52
    | exact resolve eq52 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq9
    | exact resolve eq9 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = X1 ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq168 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq171 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq162 X0 X1
       have i₂ := eq121 X1
       grind)
    | exact superpose eq121 eq162
    | (have j0 := eq162 X0 X1
       grind)
    | exact resolve eq162 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq204 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq12 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq138 X0
       grind)
    | exact superpose eq138 eq12
    | (have j0 := eq12 (σ X0) (σ (M.op X0 X0))
       grind)
    | (have r₁ := eq12 (σ X0) (σ (M.op X0 X0))
       have r₂ := eq138 X0
       grind)
    | exact resolve eq12 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq204 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq209 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq207 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq207
    | exact resolve eq207 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq216 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq209 X0
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq209
    | exact resolve eq209 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq310 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
  have eq316 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (σ X1) (σ X0)
       have i₂ := eq171 X1 X0
       grind)
    | exact superpose eq171 eq52
    | (have j1 := eq171 X1 X0
       grind)
    | exact resolve eq52 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq1845 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq168 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq168
    | exact resolve eq168 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq1886 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1845 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1845
    | (have j0 := eq1845 X0 X1
       grind)
    | exact resolve eq1845 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1845
  have eq3068 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq310
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq310
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq310 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq3069 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq3068
  have eq3078 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ (k X0 X1))) (σ (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq316 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq316
    | (have j0 := eq316 (τ X0) (τ X1)
       grind)
    | exact resolve eq316 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq316
  have eq3131 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = (M.op (σ (τ (k X0 X1))) X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3078 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3078
    | (have j0 := eq3078 X0 X1
       grind)
    | exact resolve eq3078 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3078
  have eq3142 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = (M.op (k X0 X1) X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3131 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3131
    | (have j0 := eq3131 X0 X1
       grind)
    | exact resolve eq3131 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3131
  have eq3149 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X0 X1) X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3142 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3142
    | (have j0 := eq3142 X0 X1
       grind)
    | exact resolve eq3142 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3142
  have eq3151 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = (M.op (k X0 X1) X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3149 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3149
    | (have j0 := eq3149 X0 X1
       grind)
    | exact resolve eq3149 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3149
  have eq3152 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X1) = (M.op (k X0 X1) X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3151 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3151
    | (have j0 := eq3151 X0 X1
       grind)
    | exact resolve eq3151 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3151
  have eq3153 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op (k X0 X1) X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3152 X0 X1
       have i₂ := eq125 X0
       grind)
    | exact superpose eq125 eq3152
    | (have j0 := eq3152 X0 X1
       grind)
    | exact resolve eq3152 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq3152
  have eq3154 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op (k X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3153 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3153
    | (have j0 := eq3153 X0 X1
       grind)
    | exact resolve eq3153 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3153
  have eq3155 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X0 X1) X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3154 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3154
    | (have j0 := eq3154 X0 X1
       grind)
    | exact resolve eq3154 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3154
  have eq39497 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq140 y (σ x)
       have i₂ := eq3069
       grind)
    | exact superpose eq3069 eq140
    | (have j0 := eq140 y (σ x)
       grind)
    | (have r₁ := eq140 y (σ x)
       have r₂ := eq3069
       grind)
    | exact resolve eq140 eq3069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq3069
  have eq39554 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq39497
  have eq39555 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq39554
  have eq39589 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39555
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq39555
    | exact resolve eq39555 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39555
  have eq39611 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39589
       have i₂ := eq121 x
       grind)
    | exact superpose eq121 eq39589
    | exact resolve eq39589 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39589
  have eq411010 : (k y x) = (τ (σ (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq39611
       grind)
    | exact superpose eq39611 eq10
    | exact resolve eq10 eq39611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39611
  have eq411452 : (k y x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq411010
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq411010
    | exact resolve eq411010 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411010
  have eq411458 : (σ x) = (M.op (σ x) (σ y)) ∨ (k y x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq411452
       have r₂ := eq13 y x
       grind)
    | exact resolve eq411452 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411452
  have eq411487 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (σ x) X0) (σ y)) ∨ (k y x) = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ x)
       have i₂ := eq411458
       grind)
    | exact superpose eq411458 eq9
    | exact resolve eq9 eq411458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411488 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (k y x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq411458
       grind)
    | exact superpose eq411458 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq411458
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq411458
       grind)
    | exact resolve eq12 eq411458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411595 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (k y x) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq411488
  have eq411644 : (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq411595
       have i₂ := eq121 y
       grind)
    | exact superpose eq121 eq411595
    | exact resolve eq411595 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411595
  have eq411680 : (σ (k y x)) = (σ (M.op y y)) ∨ (k y x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq411644
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq411644
    | exact resolve eq411644 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411644
  have eq411728 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) ∨ (k y x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1886 x y
       have i₂ := eq411680
       grind)
    | exact superpose eq411680 eq1886
    | (have j0 := eq1886 x y
       grind)
    | exact resolve eq1886 eq411680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886 eq411680
  have eq412066 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) ∨ (k y x) = (M.op x x) := by grind
  clear eq411728
  have eq412180 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ (k y x) = (M.op x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq412066
       have r₂ := eq13 y x
       grind)
    | exact resolve eq412066 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412066
  have eq416992 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (k y x) = (M.op x x) ∨ x = (M.op x y) ∨ (k y x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq411487 (σ y)
       have i₂ := eq411458
       grind)
    | exact superpose eq411458 eq411487
    | exact resolve eq411487 eq411458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411458 eq411487
  have eq417163 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (k y x) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq416992
  have eq417185 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (k y x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq417163
       have i₂ := eq121 y
       grind)
    | exact superpose eq121 eq417163
    | exact resolve eq417163 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq417163
  have eq417209 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (k y x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq417185
       grind)
    | exact superpose eq417185 eq16
    | exact resolve eq16 eq417185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417185
  have eq417400 : (k y x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq417209
       have r₂ := eq412180
       grind)
    | exact resolve eq417209 eq412180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412180 eq417209
  have eq417448 : (M.op x y) = (M.op x x) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq417400
       grind)
    | exact superpose eq417400 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq417400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417473 : (M.op y x) = (M.op (M.op x x) x) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3155 y x
       have i₂ := eq417400
       grind)
    | exact superpose eq417400 eq3155
    | (have j0 := eq3155 y x
       grind)
    | exact resolve eq3155 eq417400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3155 eq417400
  have eq417558 : (M.op y x) = (M.op (M.op x x) x) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq417473
  have eq417562 : (M.op y y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq417448
  have eq417570 : (M.op y y) = (M.op y x) ∨ (M.op y x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq417558
       have i₂ := eq52 x x
       grind)
    | exact superpose eq52 eq417558
    | exact resolve eq417558 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417558
  have eq419290 : (M.op y x) = (M.op (M.op y x) y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52 y y
       have i₂ := eq417562
       grind)
    | exact superpose eq417562 eq52
    | exact resolve eq52 eq417562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417562
  have eq419407 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq419290
       have i₂ := eq52 y x
       grind)
    | exact superpose eq52 eq419290
    | exact resolve eq419290 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419290
  have eq419820 : (M.op y x) = (M.op (M.op y x) y) ∨ (M.op y x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52 y y
       have i₂ := eq417570
       grind)
    | exact superpose eq417570 eq52
    | exact resolve eq52 eq417570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417570
  have eq419937 : (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq419820
       have i₂ := eq52 y x
       grind)
    | exact superpose eq52 eq419820
    | exact resolve eq419820 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419820
  have eq420192 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq419937
  have eq420196 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq420192
       have r₂ := eq419407
       grind)
    | exact resolve eq420192 eq419407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420192
  have eq420204 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op (M.op x y) X0) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq420196
       grind)
    | exact superpose eq420196 eq9
    | exact resolve eq9 eq420196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420206 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52 y x
       have i₂ := eq420196
       grind)
    | exact superpose eq420196 eq52
    | exact resolve eq52 eq420196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420213 : (M.op x y) ≠ (M.op x y) ∨ (M.op y y) = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq68 x y
       have i₂ := eq420196
       grind)
    | exact superpose eq420196 eq68
    | (have r₁ := eq68 x y
       have r₂ := eq420196
       grind)
    | (have r₁ := eq68 y x
       have r₂ := eq420196
       grind)
    | exact resolve eq68 eq420196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq420324 : (M.op y y) = (k y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq420213
  have eq421645 : (M.op y y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9 y y x
       have i₂ := eq420206
       grind)
    | exact superpose eq420206 eq9
    | exact resolve eq9 eq420206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq422022 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq420206
       have i₂ := eq421645
       grind)
    | exact superpose eq421645 eq420206
    | exact resolve eq420206 eq421645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420206 eq421645
  have eq422166 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq422022
  have eq422189 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq138 y
       have i₂ := eq422166
       grind)
    | exact superpose eq422166 eq138
    | exact resolve eq138 eq422166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq422199 : (σ (M.op x y)) = (σ (k y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq216 y
       have i₂ := eq422166
       grind)
    | exact superpose eq422166 eq216
    | exact resolve eq216 eq422166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq422166
  have eq424639 : (M.op x x) = (M.op (M.op y x) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq420204 x
       have i₂ := eq52 x y
       grind)
    | exact superpose eq52 eq420204
    | exact resolve eq420204 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420204
  have eq424817 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq424639
       have i₂ := eq420196
       grind)
    | exact superpose eq420196 eq424639
    | exact resolve eq424639 eq420196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420196 eq424639
  have eq424965 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq424817
  have eq424978 : (M.op y x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq424965
       have i₂ := eq52 x y
       grind)
    | exact superpose eq52 eq424965
    | exact resolve eq424965 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424965
  have eq426805 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq419407
       have i₂ := eq424978
       grind)
    | exact superpose eq424978 eq419407
    | exact resolve eq419407 eq424978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419407
  have eq426808 : (M.op x y) = (M.op (M.op x x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52 y x
       have i₂ := eq424978
       grind)
    | exact superpose eq424978 eq52
    | exact resolve eq52 eq424978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424978
  have eq426933 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq426805
  have eq427071 : x ≠ (M.op x x) ∨ x = (M.op x y) := by grind
  have eq428956 : (M.op x y) ≠ (M.op x x) ∨ (M.op y y) = (k y (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y (M.op x x)
       have i₂ := eq426808
       grind)
    | exact superpose eq426808 eq12
    | (have j0 := eq12 y (M.op x x)
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq426808
       grind)
    | exact resolve eq12 eq426808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426808
  have eq429089 : (M.op y y) = (k y (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq428956
       have r₂ := eq426933
       grind)
    | exact resolve eq428956 eq426933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428956
  have eq429186 : (σ (M.op x x)) = (σ (k y (M.op x x))) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq422199
       have i₂ := eq426933
       grind)
    | exact superpose eq426933 eq422199
    | exact resolve eq422199 eq426933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429187 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq422199
       have i₂ := eq420324
       grind)
    | exact superpose eq420324 eq422199
    | exact resolve eq422199 eq420324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420324 eq422199
  have eq429544 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by grind
  clear eq429187
  have eq429655 : (σ (M.op x x)) = (σ (k y (M.op x x))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq429186
       have r₂ := eq427071
       grind)
    | exact resolve eq429186 eq427071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429186
  have eq430663 : (σ (M.op y y)) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq429655
       have i₂ := eq429089
       grind)
    | exact superpose eq429089 eq429655
    | exact resolve eq429655 eq429089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429089 eq429655
  have eq431015 : (σ (M.op y y)) = (σ (M.op x x)) ∨ x = (M.op x y) := by grind
  clear eq430663
  have eq431146 : (σ (M.op x y)) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq429544
       have i₂ := eq431015
       grind)
    | exact superpose eq431015 eq429544
    | exact resolve eq429544 eq431015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429544 eq431015
  have eq431525 : (σ (M.op x y)) = (σ (M.op x x)) ∨ x = (M.op x y) := by grind
  clear eq431146
  have eq437107 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq422189
       have i₂ := eq426933
       grind)
    | exact superpose eq426933 eq422189
    | exact resolve eq422189 eq426933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422189 eq426933
  have eq437315 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq437107
       have r₂ := eq427071
       grind)
    | exact resolve eq437107 eq427071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427071 eq437107
  have eq445236 : (M.op (σ y) (σ x)) = (M.op (σ (M.op x x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq139 x (σ y)
       have i₂ := eq437315
       grind)
    | exact superpose eq437315 eq139
    | exact resolve eq139 eq437315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq445426 : (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq445236
       have i₂ := eq138 x
       grind)
    | exact superpose eq138 eq445236
    | exact resolve eq445236 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445236
  have eq445647 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52 (σ y) (σ x)
       have i₂ := eq445426
       grind)
    | exact superpose eq445426 eq52
    | exact resolve eq52 eq445426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq445426
  have eq484353 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq437315
       have i₂ := eq445647
       grind)
    | exact superpose eq445647 eq437315
    | exact resolve eq437315 eq445647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437315 eq445647
  have eq484524 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x y) := by grind
  clear eq484353
  have eq486472 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq484524
       grind)
    | exact superpose eq484524 eq16
    | exact resolve eq16 eq484524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484524
  have eq486706 : x = (M.op x y) := by
    first
    | (have r₁ := eq486472
       have r₂ := eq431525
       grind)
    | exact resolve eq486472 eq431525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431525 eq486472
  have eq486797 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op x X0) y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq486706
       grind)
    | exact superpose eq486706 eq9
    | exact resolve eq9 eq486706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq487511 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq486797 y
       have i₂ := eq486706
       grind)
    | exact superpose eq486706 eq486797
    | exact resolve eq486797 eq486706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486797
  have eq487698 : x = (M.op y y) := by
    first
    | (have i₁ := eq487511
       have i₂ := eq486706
       grind)
    | exact superpose eq486706 eq487511
    | exact resolve eq487511 eq486706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487511
  have eq489452 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq138 y
       have i₂ := eq487698
       grind)
    | exact superpose eq487698 eq138
    | exact resolve eq138 eq487698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq487698
  have eq490678 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq489452
       grind)
    | exact superpose eq489452 eq16
    | exact resolve eq16 eq489452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489452
  have eq490891 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq490678
       have i₂ := eq486706
       grind)
    | exact superpose eq486706 eq490678
    | exact resolve eq490678 eq486706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486706 eq490678
  have eq490892 : False := by grind
  exact eq490892

/-- `Equation4209`: `x ◇ y = ((z ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_y_pxx_pyx_Equation4209 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4209 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4209.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X2 X1) X0) X1) := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq22 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq48 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
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
  have eq59 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq47 eq16
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq66 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq45
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq78 : (k x y) = (τ (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq59
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq59
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq59 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq38
    | (have j1 := eq11 (σ (k y X0)) (M.op (σ X0) (σ y))
       grind)
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq83
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq83
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq83 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq83
       grind)
    | exact superpose eq83 eq16
    | exact resolve eq16 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq88
    | exact resolve eq88 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq22 eq94
    | exact resolve eq94 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  have eq101 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq84
       grind)
    | exact superpose eq84 eq16
    | exact resolve eq16 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq39 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq39
    | exact resolve eq39 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq159 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  have eq165 : (σ (k (k y x) y)) = (k (k (σ y) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq42 (k y x)
       have i₂ := eq83
       grind)
    | exact superpose eq83 eq42
    | exact resolve eq42 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq203 : (M.op y x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq51 x y
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq51
    | (have j0 := eq51 x y
       grind)
    | exact resolve eq51 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0) X1
       have i₂ := eq51 X1 X0
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq16
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq370 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (σ X0) (σ X0)
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq51
    | (have j1 := eq64 X0
       grind)
    | exact resolve eq51 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq64 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq478 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (σ X1) (σ X0)
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq51
    | (have j1 := eq71 X0 X1
       grind)
    | exact resolve eq51 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op (M.op (σ (k X0 X1)) X2) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (σ X0) (σ X1)
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq14
    | (have j1 := eq71 X0 X1
       grind)
    | exact resolve eq14 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq510 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq257 X0 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq257
    | (have j0 := eq257 X0 x
       grind)
    | exact resolve eq257 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq512 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq22 eq257
    | (have j0 := eq257 X0 (M.op x y)
       grind)
    | exact resolve eq257 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3216 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  have eq5059 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq370
  have eq6912 : ∀ X0 X1 : G, (M.op (σ y) (σ X0)) = (M.op (σ (k y (k X0 X1))) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (σ y) ∨ (σ y) = (M.op (σ (k X0 X1)) (σ (k X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq86 eq479
    | (have j0 := eq479 X0 X1 x
       have j1 := eq86 (k X0 X1)
       grind)
    | exact resolve eq479 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq479
  have eq10084 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq95 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq10085 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq10084
    | exact resolve eq10084 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10084
  have eq10096 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq10085
       have r₂ := eq29
       grind)
    | exact resolve eq10085 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10085
  have eq10098 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq10096
  have eq10111 : (τ (σ x)) = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq10098 eq93
    | exact resolve eq93 eq10098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq10098
  have eq10132 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k y x) := by
    first
    | exact superpose eq30 eq10111
    | exact resolve eq10111 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10111
  have eq11018 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k y x) := by grind
  clear eq10132
  have eq11025 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11018
  have eq11031 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq83
       have i₂ := eq11025
       grind)
    | exact superpose eq11025 eq83
    | exact resolve eq83 eq11025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11036 : (σ (k x y)) = (k (k (σ y) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq165
       have i₂ := eq11025
       grind)
    | exact superpose eq11025 eq165
    | exact resolve eq165 eq11025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq11039 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq478 y x
       have i₂ := eq11025
       grind)
    | exact superpose eq11025 eq478
    | (have j0 := eq478 x y
       grind)
    | exact resolve eq478 eq11025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq11040 : x = (M.op x y) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq11025
       grind)
    | exact superpose eq11025 eq11
    | (have j0 := eq11 x (M.op x y)
       grind)
    | exact resolve eq11 eq11025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11041 : x = (M.op x y) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq11040
  have eq11043 : y = (M.op x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11041
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq11041
    | exact resolve eq11041 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11041
  have eq11044 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11039
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11039
    | exact resolve eq11039 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11039
  have eq11047 : (k (σ x) (σ y)) = (k (k (σ y) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11036
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq11036
    | exact resolve eq11036 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq11036
  have eq11052 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11031
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11031
    | exact resolve eq11031 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11031
  have eq11054 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11044
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq11044
    | exact resolve eq11044 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11044
  have eq11056 : (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11054
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq11054
    | exact resolve eq11054 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11054
  have eq11058 : (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11056
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11056
    | exact resolve eq11056 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11056
  have eq11059 : (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq11058
  have eq11062 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq11059
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11059
    | exact resolve eq11059 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11059
  have eq11064 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq11062
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq11062
    | exact resolve eq11062 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11062
  have eq11195 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11052 eq11
    | (have j0 := eq11 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq11052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11196 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq11195
  have eq11200 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq11196
    | exact resolve eq11196 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11196
  have eq11216 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq205 x x
       have i₂ := eq11043
       grind)
    | exact superpose eq11043 eq205
    | exact resolve eq205 eq11043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11043
  have eq11220 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11216
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq11216
    | exact resolve eq11216 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11216
  have eq11350 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq11200 eq205
    | exact resolve eq205 eq11200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11351 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq11200 eq51
    | exact resolve eq51 eq11200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11200
  have eq11353 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq11350
    | exact resolve eq11350 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11350
  have eq11484 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq11220
       grind)
    | exact superpose eq11220 eq96
    | exact resolve eq96 eq11220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11486 : y = (k (M.op x y) y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq11220
  have eq11493 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22 eq11484
    | exact resolve eq11484 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11484
  have eq11597 : (σ y) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  have eq11962 : (k (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11047
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq11047
    | (have j1 := eq11 (k (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact resolve eq11047 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11047
  have eq11968 : (k (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq11962
  have eq11971 : (k (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq28 eq11968
    | exact resolve eq11968 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11968
  have eq14177 : (τ (σ (M.op x y))) = (k y y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq11493 eq101
    | exact resolve eq101 eq11493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq14198 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq32 eq14177
    | exact resolve eq14177 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14177
  have eq848627 : (M.op (σ y) (σ y)) = (M.op (σ (k y x)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6912 y x
       have i₂ := eq11025
       grind)
    | exact superpose eq11025 eq6912
    | (have j0 := eq6912 x y
       grind)
    | exact resolve eq6912 eq11025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6912 eq11025
  have eq849723 : (M.op (σ y) (σ y)) = (M.op (σ (k y x)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq848627
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq848627
    | exact resolve eq848627 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848627
  have eq850270 : (M.op (σ y) (σ y)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq849723
       have i₂ := eq83
       grind)
    | exact superpose eq83 eq849723
    | exact resolve eq849723 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq849723
  have eq850788 : (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq850270
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq850270
    | exact resolve eq850270 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850270
  have eq850789 : (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq850788
  have eq851224 : (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq850789
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq850789
    | exact resolve eq850789 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850789
  have eq851225 : (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq851224
  have eq851552 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq851225
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq851225
    | exact resolve eq851225 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851225
  have eq851816 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq851552
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq851552
    | exact resolve eq851552 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851552
  have eq852028 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq851816
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq851816
    | exact resolve eq851816 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851816
  have eq852029 : (M.op (σ y) (σ y)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq852028
  have eq852304 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11052 eq852029
    | exact resolve eq852029 eq11052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11052 eq852029
  have eq852366 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq852304
  have eq852369 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq28 eq852366
    | exact resolve eq852366 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852366
  have eq852401 : (σ y) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq852369
  have eq852461 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq852401 eq11971
    | exact resolve eq11971 eq852401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11971 eq852401
  have eq852488 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq852461
  have eq858464 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq852488 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq852488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852488
  have eq858484 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq858464
  have eq1089559 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq858484 eq11064
    | exact resolve eq11064 eq858484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11064 eq858484
  have eq1089625 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1089559
  have eq1089680 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1089625 eq205
    | exact resolve eq205 eq1089625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq1089625
  have eq1089738 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq28 eq1089680
    | exact resolve eq1089680 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089680
  have eq1095249 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  have eq1412263 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq11353 eq159
    | exact resolve eq159 eq11353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11353
  have eq1420172 : (k (σ y) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq84
       have i₂ := eq1412263
       grind)
    | exact superpose eq1412263 eq84
    | exact resolve eq84 eq1412263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq1412263
  have eq1420417 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1420172
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq1420172
    | exact resolve eq1420172 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420172
  have eq1420651 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1420417 eq11493
    | exact resolve eq11493 eq1420417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420417
  have eq1420757 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1420651
  have eq1420771 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1420757
       have r₂ := eq29
       grind)
    | exact resolve eq1420757 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420757
  have eq1426130 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1420771 eq29
    | exact resolve eq29 eq1420771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1426152 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1420771 eq11597
    | exact resolve eq11597 eq1420771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11597 eq1420771
  have eq1426556 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1426152
  have eq1503725 : (τ (σ y)) = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq11351 eq78
    | exact resolve eq78 eq11351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq11351
  have eq1504488 : (τ (σ y)) = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1503725
  have eq1504506 : (τ (σ y)) = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq1504488
       have r₂ := eq1095249
       grind)
    | exact resolve eq1504488 eq1095249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504488
  have eq1504508 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | exact superpose eq31 eq1504506
    | exact resolve eq1504506 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504506
  have eq1504558 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by grind
  clear eq1504508
  have eq1506471 : (τ (σ y)) = (k x y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | exact superpose eq1504558 eq59
    | exact resolve eq59 eq1504558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq1504558
  have eq1506541 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | exact superpose eq31 eq1506471
    | exact resolve eq1506471 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506471
  have eq1506542 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1506541
  have eq1506585 : y = (M.op y x) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq1506542
       grind)
    | exact superpose eq1506542 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq1506542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506542
  have eq1506609 : y = (M.op y x) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq1506585
  have eq1509309 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq51 y x
       have i₂ := eq1506609
       grind)
    | exact superpose eq1506609 eq51
    | exact resolve eq51 eq1506609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1506609
  have eq1509378 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1509309
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq1509309
    | exact resolve eq1509309 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1509309
  have eq1509885 : x ≠ (M.op x y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq1509378
  have eq1941165 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1426556 eq11493
    | exact resolve eq11493 eq1426556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11493 eq1426556
  have eq1941290 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1941165
  have eq1941319 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1941290
       have r₂ := eq1426130
       grind)
    | exact resolve eq1941290 eq1426130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426130 eq1941290
  have eq1941505 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1941319 eq1095249
    | (have r₁ := eq1095249
       have r₂ := eq1941319
       grind)
    | exact resolve eq1095249 eq1941319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095249 eq1941319
  have eq1941538 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1941505
  have eq1941539 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1941538
  have eq1942345 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1941539 eq159
    | exact resolve eq159 eq1941539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq1941539
  have eq1942452 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1942345
  have eq1942469 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq1942452
    | exact resolve eq1942452 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1942452
  have eq1943314 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14198
       have i₂ := eq1942469
       grind)
    | exact superpose eq1942469 eq14198
    | exact resolve eq14198 eq1942469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14198 eq1942469
  have eq1943437 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1943314
  have eq1943754 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1943437 eq31
    | exact resolve eq31 eq1943437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1943437
  have eq1943999 : x = y ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq1943754
    | exact resolve eq1943754 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1943754
  have eq1944000 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1943999
  have eq1944607 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1944000 eq22
    | exact resolve eq22 eq1944000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1945158 : y = (k y y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1944000 eq11486
    | exact resolve eq11486 eq1944000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11486 eq1944000
  have eq1946002 : y = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1945158
  have eq1946539 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1944607
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq1944607
    | exact resolve eq1944607 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1944607
  have eq1981949 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq372 y
       have i₂ := eq1946002
       grind)
    | exact superpose eq1946002 eq372
    | (have j0 := eq372 y
       grind)
    | exact resolve eq372 eq1946002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1946002
  have eq1982023 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1981949
  have eq1982103 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1982023
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq1982023
    | exact resolve eq1982023 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1982023
  have eq1985961 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1982103 eq1089738
    | exact resolve eq1089738 eq1982103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089738 eq1982103
  have eq1986007 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1985961
  have eq1986044 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1986007 eq29
    | exact resolve eq29 eq1986007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1986007
  have eq1986585 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1986044
       have r₂ := eq1946539
       grind)
    | exact resolve eq1986044 eq1946539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1946539 eq1986044
  have eq1986618 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1986585 eq31
    | exact resolve eq31 eq1986585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1986585
  have eq1986894 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq1986618
    | exact resolve eq1986618 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1986618
  have eq1986895 : x = (M.op x y) ∨ x = y := by grind
  clear eq1986894
  have eq1986897 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1986895 eq22
    | exact resolve eq22 eq1986895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1986899 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op x X0) y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1986895 eq48
    | exact resolve eq48 eq1986895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq1986903 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1986895 eq102
    | exact resolve eq102 eq1986895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq1986946 : (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1986895 eq203
    | exact resolve eq203 eq1986895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq1986965 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ (M.op x y)))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1986895 eq512
    | exact resolve eq512 eq1986895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq1987772 : x ≠ x ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1986895 eq1509885
    | (have r₁ := eq1509885
       have r₂ := eq1986895
       grind)
    | exact resolve eq1509885 eq1986895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1509885
  have eq1987811 : x ≠ x ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq1987772
  have eq1987812 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1987811
  have eq1988551 : ∀ X0 : G, (τ (k X0 (σ x))) = (τ (k X0 (σ (M.op x y)))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1986965 X0
       have i₂ := eq510 X0
       grind)
    | exact superpose eq510 eq1986965
    | exact resolve eq1986965 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510 eq1986965
  have eq1988607 : ∀ X0 : G, (k (σ x) X0) = (k (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1986903 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq1986903
    | exact resolve eq1986903 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1986903
  have eq1988612 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq1986897
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1986897
    | exact resolve eq1986897 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1986897
  have eq1993471 : ∀ X0 : G, (k (τ (σ x)) X0) = (τ (k (σ (M.op x y)) (σ X0))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1988607 eq257
    | exact resolve eq257 eq1988607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1988607
  have eq1995262 : ∀ X0 : G, (k (τ (σ (M.op x y))) X0) = (k (τ (σ x)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1993471 x
       have i₂ := eq257 sF1 x
       grind)
    | exact superpose eq257 eq1993471
    | exact resolve eq1993471 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257 eq1993471
  have eq1995459 : ∀ X0 : G, (k x X0) = (k (τ (σ (M.op x y))) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq30 eq1995262
    | exact resolve eq1995262 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1995262
  have eq1995572 : ∀ X0 : G, (k x X0) = (k (M.op x y) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq32 eq1995459
    | exact resolve eq1995459 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1995459
  have eq2025254 : (M.op y y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq1986899 y
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq1986899
    | (have j0 := eq1986899 y
       grind)
    | exact resolve eq1986899 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1986899
  have eq2025418 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1986895 eq2025254
    | exact resolve eq2025254 eq1986895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1986895 eq2025254
  have eq2025510 : (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq2025418
  have eq2025516 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq2025510
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq2025510
    | exact resolve eq2025510 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2025510
  have eq2025572 : y = (k (M.op x y) y) ∨ x = y := by grind
  clear eq2025516
  have eq2025784 : y = (k x y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2025572 eq1995572
    | exact resolve eq1995572 eq2025572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1995572 eq2025572
  have eq2025816 : y = (k x y) ∨ x = y := by grind
  clear eq2025784
  have eq2026343 : y = (M.op y x) ∨ x = y ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq2025816
       grind)
    | exact superpose eq2025816 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq2025816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2025816
  have eq2026367 : y = (M.op y x) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq2026343
  have eq2029992 : (τ (σ x)) = (τ (k (M.op (σ x) (σ x)) (σ (M.op x y)))) ∨ x = y := by grind
  have eq2031860 : x = (τ (k (M.op (σ x) (σ x)) (σ (M.op x y)))) ∨ x = y := by
    first
    | exact superpose eq30 eq2029992
    | exact resolve eq2029992 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2029992
  have eq2215170 : y = (M.op x x) ∨ x = y ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1986946
       have i₂ := eq2026367
       grind)
    | exact superpose eq2026367 eq1986946
    | exact resolve eq1986946 eq2026367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1986946 eq2026367
  have eq2215231 : y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq2215170
  have eq2222332 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq66
       have i₂ := eq2215231
       grind)
    | exact superpose eq2215231 eq66
    | exact resolve eq66 eq2215231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2222367 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3216 x
       have i₂ := eq2215231
       grind)
    | exact superpose eq2215231 eq3216
    | (have j0 := eq3216 x
       grind)
    | exact resolve eq3216 eq2215231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3216 eq2215231
  have eq2222404 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq2222367
  have eq2222436 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq2222332
  have eq2222452 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2222404
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq2222404
    | exact resolve eq2222404 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2222404
  have eq2222457 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2222436
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq2222436
    | exact resolve eq2222436 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2222436
  have eq2222462 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2222452
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2222452
    | exact resolve eq2222452 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2222452
  have eq2222467 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq2222462
       have r₂ := eq1987812
       grind)
    | exact resolve eq2222462 eq1987812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1987812 eq2222462
  have eq2222470 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2222467
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2222467
    | exact resolve eq2222467 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2222467
  have eq2222953 : (τ (σ y)) = (τ (k (σ x) (σ (M.op x y)))) ∨ x = y ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq2222457 eq1988551
    | exact resolve eq1988551 eq2222457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1988551 eq2222457
  have eq2223040 : (τ (σ y)) = (τ (k (σ x) (σ (M.op x y)))) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq2222953
  have eq2223116 : (τ (σ y)) = (k x (M.op x y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq63 eq2223040
    | exact resolve eq2223040 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2223040
  have eq2223153 : y = (k x (M.op x y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq31 eq2223116
    | exact resolve eq2223116 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2223116
  have eq2223195 : x = (τ (k (σ x) (σ (M.op x y)))) ∨ x = y ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq2222470 eq2031860
    | exact resolve eq2031860 eq2222470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2031860 eq2222470
  have eq2223227 : x = (τ (k (σ x) (σ (M.op x y)))) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq2223195
  have eq2223271 : x = (k x (M.op x y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq63 eq2223227
    | exact resolve eq2223227 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq2223227
  have eq2229024 : x = y ∨ x = y ∨ x = (M.op y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq2223271 eq2223153
    | exact resolve eq2223153 eq2223271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2223153 eq2223271
  have eq2229075 : x = (M.op y y) ∨ x = y := by grind
  clear eq2229024
  have eq2229203 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq96
       have i₂ := eq2229075
       grind)
    | exact superpose eq2229075 eq96
    | exact resolve eq96 eq2229075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq2229247 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq5059 y
       have i₂ := eq2229075
       grind)
    | exact superpose eq2229075 eq5059
    | (have j0 := eq5059 y
       grind)
    | exact resolve eq5059 eq2229075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5059 eq2229075
  have eq2229282 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq2229247
  have eq2229310 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by grind
  clear eq2229203
  have eq2229324 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2229282
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq2229282
    | exact resolve eq2229282 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2229282
  have eq2229328 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2229310
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2229310
    | exact resolve eq2229310 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2229310
  have eq2229332 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2229324
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2229324
    | exact resolve eq2229324 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2229324
  have eq2229337 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq2229332
    | exact resolve eq2229332 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2229332
  have eq2229341 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2229337
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq2229337
    | exact resolve eq2229337 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2229337
  have eq2231532 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq2229341
  have eq2232223 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2231532 eq2229328
    | exact resolve eq2229328 eq2231532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2229328 eq2231532
  have eq2232310 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2232223
  have eq2232419 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2232310 eq29
    | exact resolve eq29 eq2232310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2232310
  have eq2232798 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2232419
       have r₂ := eq1988612
       grind)
    | exact resolve eq2232419 eq1988612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1988612 eq2232419
  have eq2232801 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2232798 eq31
    | exact resolve eq31 eq2232798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2232798
  have eq2233419 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq2232801
    | exact resolve eq2232801 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2232801
  have eq2233420 : x = y := by grind
  clear eq2233419
  have eq2233421 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq2233420
       grind)
    | exact superpose eq2233420 eq20
    | exact resolve eq20 eq2233420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2233422 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq2233420
       grind)
    | exact superpose eq2233420 eq26
    | exact resolve eq26 eq2233420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2233420
  have eq2234498 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2233422
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2233422
    | exact resolve eq2233422 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2233422
  have eq2234501 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2234498 eq28
    | exact resolve eq28 eq2234498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2234498
  have eq2235085 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq66
       have i₂ := eq2233421
       grind)
    | exact superpose eq2233421 eq66
    | exact resolve eq66 eq2233421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq2235141 : x = (k (M.op x y) x) := by grind
  clear eq2233421
  have eq2235186 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22 eq2235085
    | exact resolve eq2235085 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2235085
  have eq2235273 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq2237345 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq2237511 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2234501 eq2237345
    | exact resolve eq2237345 eq2234501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2237345
  have eq2237559 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2237511
       have r₂ := eq29
       grind)
    | exact resolve eq2237511 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2237511
  have eq2237583 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2234501 eq2237559
    | exact resolve eq2237559 eq2234501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2237559
  have eq2237614 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2237583 eq29
    | exact resolve eq29 eq2237583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2237808 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2237583 eq2235273
    | exact resolve eq2235273 eq2237583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2235273 eq2237583
  have eq2238970 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2237808 eq2235186
    | exact resolve eq2235186 eq2237808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2235186 eq2237808
  have eq2239072 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq2238970
  have eq2239162 : x = (M.op x y) := by
    first
    | (have r₁ := eq2239072
       have r₂ := eq2237614
       grind)
    | exact resolve eq2239072 eq2237614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2237614 eq2239072
  have eq2239265 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2239162 eq22
    | exact resolve eq22 eq2239162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq2240296 : x = (k x x) := by
    first
    | exact superpose eq2239162 eq2235141
    | exact resolve eq2235141 eq2239162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2235141 eq2239162
  have eq2240815 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2239265
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2239265
    | exact resolve eq2239265 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2239265
  have eq2243388 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq372 x
       have i₂ := eq2240296
       grind)
    | exact superpose eq2240296 eq372
    | (have j0 := eq372 x
       grind)
    | exact resolve eq372 eq2240296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq2240296
  have eq2243467 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2243388
  have eq2243549 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2243467
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2243467
    | exact resolve eq2243467 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2243467
  have eq2243665 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2234501 eq2243549
    | exact resolve eq2243549 eq2234501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2234501 eq2243549
  have eq2243774 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2240815 eq2243665
    | exact resolve eq2243665 eq2240815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2240815 eq2243665
  have eq2243881 : False := by grind
  exact eq2243881

/-- `Equation4209`: `x ◇ y = ((z ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pyx_y_pyx_Equation4209 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4209 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4209.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
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
  have eq65 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (M.op X1 X0) X1
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq336 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
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
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq14 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq336 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq343 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq338 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq344 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq343 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq343 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq343 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq355 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq344 (σ X0)
       grind)
    | exact superpose eq344 eq15
    | exact resolve eq15 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq355 X0
       have i₂ := eq344 X0
       grind)
    | exact superpose eq344 eq355
    | exact resolve eq355 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344 eq355
  have eq420 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq65 (σ X0) (σ X0)
       have i₂ := eq374 X0
       grind)
    | exact superpose eq374 eq65
    | exact resolve eq65 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq420 X0
       have i₂ := eq374 (M.op X0 X0)
       grind)
    | exact superpose eq374 eq420
    | exact resolve eq420 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq432 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq428 X0
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq428
    | exact resolve eq428 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq428
  have eq702 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq339 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq703 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq702 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq718 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq703 (σ X1) (σ X0)
       grind)
    | exact superpose eq703 eq15
    | (have j1 := eq703 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq726 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq703 (τ X1) X0
       grind)
    | exact superpose eq703 eq18
    | (have j1 := eq703 (τ X1) X0
       grind)
    | exact resolve eq18 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq703
  have eq735 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq718 X0 X1
       have i₂ := eq374 X0
       grind)
    | exact superpose eq374 eq718
    | (have j0 := eq718 X0 X1
       grind)
    | exact resolve eq718 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374 eq718
  have eq1064 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq726 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq726
    | exact resolve eq726 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq1125 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1064 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1064
    | (have j0 := eq1064 X0 X1
       grind)
    | exact resolve eq1064 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq2133 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq735 x y
       grind)
    | exact superpose eq735 eq16
    | (have j1 := eq735 x y
       grind)
    | exact resolve eq16 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq2273 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2133
       have i₂ := eq1125 y x
       grind)
    | exact superpose eq1125 eq2133
    | (have j1 := eq1125 y x
       grind)
    | (have r₁ := eq2133
       have r₂ := eq1125 y x
       grind)
    | exact resolve eq2133 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125 eq2133
  have eq2274 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq2273
  have eq2285 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq432 x
       have i₂ := eq2274
       grind)
    | exact superpose eq2274 eq432
    | exact resolve eq432 eq2274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274
  have eq2312 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq2285
       have r₂ := eq16
       grind)
    | exact resolve eq2285 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2285
  have eq2319 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2312
       grind)
    | exact superpose eq2312 eq10
    | exact resolve eq10 eq2312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2312
  have eq2374 : y = (M.op x x) := by
    first
    | (have i₁ := eq2319
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2319
    | exact resolve eq2319 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319
  have eq2401 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq432 x
       have i₂ := eq2374
       grind)
    | exact superpose eq2374 eq432
    | exact resolve eq432 eq2374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432 eq2374
  have eq2428 : False := by grind
  exact eq2428
