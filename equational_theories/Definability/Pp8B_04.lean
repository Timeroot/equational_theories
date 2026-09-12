import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1434`: `x = (x ◇ x) ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation1434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq267 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq267 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq270 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq268 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq268 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq268 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq281 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq270 (σ X0)
       grind)
    | exact superpose eq270 eq15
    | exact resolve eq15 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq281 X0
       have i₂ := eq270 X0
       grind)
    | exact superpose eq270 eq281
    | exact resolve eq281 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq281
  have eq343 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq348 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq343 X0 X1
       have j1 := eq344 X0 X1
       grind)
    | (have r₁ := eq343 X0 X1
       have r₂ := eq344 X0 X1
       grind)
    | exact resolve eq343 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq344
  have eq423 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq348 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq348
    | exact resolve eq348 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq423 X1 X0
       grind)
    | exact superpose eq423 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq423 X1 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq423 X0 X1
       grind)
    | exact resolve eq13 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq463 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq486 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq478 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq478 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq478 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq501 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq486 X1 (τ X0)
       grind)
    | exact superpose eq486 eq18
    | (have j1 := eq486 X1 (τ X0)
       grind)
    | exact resolve eq18 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq518 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq486 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq828 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq501 X1 (τ X0)
       grind)
    | exact superpose eq501 eq17
    | (have j1 := eq501 X1 (τ X0)
       grind)
    | exact resolve eq17 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq501
  have eq835 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq828 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq828
    | (have j0 := eq828 X0 X1
       grind)
    | exact resolve eq828 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq846 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq835 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq835
    | (have j0 := eq835 X0 X1
       grind)
    | exact resolve eq835 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq847 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq846 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq846
    | (have j0 := eq846 X0 X1
       grind)
    | exact resolve eq846 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq901 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq847 X0 X1
       have i₂ := eq486 X0 X1
       grind)
    | exact superpose eq486 eq847
    | (have j0 := eq847 X1 X0
       have j1 := eq486 X1 X0
       grind)
    | exact resolve eq847 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq902 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq847 X1 (σ X0)
       have i₂ := eq348 X0 X1
       grind)
    | exact superpose eq348 eq847
    | (have j1 := eq348 X0 X1
       grind)
    | exact resolve eq847 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348 eq847
  have eq939 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq902 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902
  have eq968 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq939 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq939
    | (have j0 := eq939 X0 X1
       grind)
    | exact resolve eq939 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939
  have eq969 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq901 X0 X1
       have j1 := eq518 X1 X0
       grind)
    | (have r₁ := eq901 X1 X0
       have r₂ := eq518 X0 X1
       grind)
    | exact resolve eq901 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq901
  have eq1022 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq969 X1 (σ X0)
       grind)
    | exact superpose eq969 eq28
    | (have j1 := eq969 X1 (σ X0)
       grind)
    | exact resolve eq28 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq969
  have eq1042 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1022 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1022
    | (have j0 := eq1022 X0 X1
       grind)
    | exact resolve eq1022 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1070 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1042 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1042
    | (have j0 := eq1042 X0 X1
       grind)
    | exact resolve eq1042 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq1417 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x (τ (σ y)))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq968 x (σ y)
       grind)
    | exact superpose eq968 eq16
    | (have j1 := eq968 x (σ y)
       grind)
    | exact resolve eq16 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq1463 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq1417
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1417
    | exact resolve eq1417 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417
  have eq1470 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have r₁ := eq1463
       have r₂ := eq16
       grind)
    | exact resolve eq1463 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463
  have eq1477 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1470
       have i₂ := eq423 x y
       grind)
    | exact superpose eq423 eq1470
    | (have j1 := eq423 x y
       grind)
    | exact resolve eq1470 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq1478 : (M.op x y) = (k y x) := by grind
  clear eq1477
  have eq2709 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1070 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1070
    | exact resolve eq1070 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070
  have eq2802 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2709 x y
       grind)
    | exact superpose eq2709 eq16
    | (have j1 := eq2709 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2709 x y
       grind)
    | exact resolve eq16 eq2709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2709
  have eq2829 : y = (k y x) := by grind
  clear eq2802
  have eq2874 : y = (M.op x y) := by
    first
    | (have i₁ := eq1478
       have i₂ := eq2829
       grind)
    | exact superpose eq2829 eq1478
    | exact resolve eq1478 eq2829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478 eq2829
  have eq2879 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1470
       have i₂ := eq2874
       grind)
    | exact superpose eq2874 eq1470
    | exact resolve eq1470 eq2874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470 eq2874
  have eq2888 : False := by grind
  exact eq2888

/-- `Equation1434`: `x = (x ◇ x) ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation1434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq264 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X2) = X0 ∨ (k X2 X0) = (M.op X0 X2) := by
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
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq267 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq269 : ∀ X0 X1 X2 : G, (M.op X0 X2) = X0 ∨ (k X1 X0) = (M.op X0 X1) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq264 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq270 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq268 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq268 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq268 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq281 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq270 (σ X0)
       grind)
    | exact superpose eq270 eq15
    | exact resolve eq15 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq281 X0
       have i₂ := eq270 X0
       grind)
    | exact superpose eq270 eq281
    | exact resolve eq281 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq281
  have eq343 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq348 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq343 X0 X1
       have j1 := eq344 X0 X1
       grind)
    | (have r₁ := eq343 X0 X1
       have r₂ := eq344 X0 X1
       grind)
    | exact resolve eq343 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq344
  have eq461 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq348 X0 (σ X1)
       grind)
    | exact superpose eq348 eq15
    | (have j1 := eq348 X0 (σ X1)
       grind)
    | exact resolve eq15 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq983 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq461 x y
       grind)
    | exact superpose eq461 eq16
    | (have j1 := eq461 x y
       grind)
    | exact resolve eq16 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1004 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq461 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq1040 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1004 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq1004
    | (have j0 := eq1004 (τ X1) (τ X0)
       grind)
    | exact resolve eq1004 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1048 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1040 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1040
    | (have j0 := eq1040 X0 X1
       grind)
    | exact resolve eq1040 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq1051 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1048 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1048
    | (have j0 := eq1048 X0 X1
       grind)
    | exact resolve eq1048 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq1052 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1051 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1051
    | (have j0 := eq1051 X0 X1
       grind)
    | exact resolve eq1051 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051
  have eq1053 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1052 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1052
    | (have j0 := eq1052 X0 X1
       grind)
    | exact resolve eq1052 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052
  have eq2367 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X0 X2) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq269 X0 X2 X1
       grind)
    | exact superpose eq269 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq269 X0 X2 X0
       grind)
    | (have r₁ := eq13 X2 X0
       have r₂ := eq269 X0 X1 X2
       grind)
    | exact resolve eq13 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq2398 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X0 X2) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2367 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2367
  have eq2416 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X0 X2) ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2398 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq2398 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq2398 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2398
  have eq2478 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2416 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2416
  have eq2479 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2478 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2478
  have eq2536 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq983
       have i₂ := eq2479 y x
       grind)
    | exact superpose eq2479 eq983
    | (have j1 := eq2479 y x
       grind)
    | exact resolve eq983 eq2479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983
  have eq2537 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2479 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479
  have eq2538 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by grind
  clear eq2536
  have eq2589 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq2537 (σ y) (σ x)
       have i₂ := eq2538
       grind)
    | exact superpose eq2538 eq2537
    | (have j0 := eq2537 (σ y) (σ x)
       grind)
    | (have r₁ := eq2537 (σ y) (σ x)
       have r₂ := eq2538
       grind)
    | exact resolve eq2537 eq2538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2538
  have eq2593 : (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) := by grind
  clear eq2589
  have eq2596 : x = (k y x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq2593
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2593
    | exact resolve eq2593 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2593
  have eq2622 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq1004 x y
       have i₂ := eq2596
       grind)
    | exact superpose eq2596 eq1004
    | (have j0 := eq1004 x y
       grind)
    | (have r₁ := eq1004 x y
       have r₂ := eq2596
       grind)
    | exact resolve eq1004 eq2596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2596
  have eq2633 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq2622
  have eq2636 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq1004 x y
       grind)
    | (have r₁ := eq2633
       have r₂ := eq1004 x y
       grind)
    | exact resolve eq2633 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004 eq2633
  have eq2640 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2636
       grind)
    | exact superpose eq2636 eq16
    | exact resolve eq16 eq2636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2642 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2537 (σ y) (σ x)
       have i₂ := eq2636
       grind)
    | exact superpose eq2636 eq2537
    | (have j0 := eq2537 (σ y) (σ x)
       grind)
    | (have r₁ := eq2537 (σ y) (σ x)
       have r₂ := eq2636
       grind)
    | exact resolve eq2537 eq2636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2537 eq2636
  have eq2646 : (σ x) = (k (σ y) (σ x)) := by grind
  clear eq2642
  have eq2649 : (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq2646
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2646
    | exact resolve eq2646 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2646
  have eq2669 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq2649
       grind)
    | exact superpose eq2649 eq10
    | exact resolve eq10 eq2649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2649
  have eq2719 : x = (k y x) := by
    first
    | (have i₁ := eq2669
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2669
    | exact resolve eq2669 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2669
  have eq2737 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1053 y x
       have i₂ := eq2719
       grind)
    | exact superpose eq2719 eq1053
    | (have j0 := eq1053 y x
       grind)
    | (have r₁ := eq1053 y x
       have r₂ := eq2719
       grind)
    | exact resolve eq1053 eq2719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053 eq2719
  have eq2746 : x = (M.op x y) := by grind
  clear eq2737
  have eq2750 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2640
       have i₂ := eq2746
       grind)
    | exact superpose eq2746 eq2640
    | exact resolve eq2640 eq2746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2640 eq2746
  have eq2760 : False := by grind
  exact eq2760

/-- `Equation1437`: `x = (x ◇ x) ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pyx_pxy_pyx_Equation1437 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1437 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1437.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq602 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq605 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq613 : ∀ X0 X1 : G, (τ X1) = (M.op X0 (τ X1)) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
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
  have eq5588 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq605 x y
       grind)
    | exact superpose eq605 eq16
    | (have j1 := eq605 y x
       grind)
    | exact resolve eq16 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5621 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq605 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq5916 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq602 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq602
    | exact resolve eq602 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq6008 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5916 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5916
    | (have j0 := eq5916 X0 X1
       grind)
    | exact resolve eq5916 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5916
  have eq16795 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) X1) ∨ (M.op X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X1) X0
       have i₂ := eq613 X0 X1
       grind)
    | exact superpose eq613 eq12
    | (have j1 := eq613 X1 X0
       grind)
    | (have r₁ := eq12 (τ X1) X0
       have r₂ := eq613 X0 X1
       grind)
    | exact resolve eq12 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq16821 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) X1) ∨ (M.op X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq16795 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16795
  have eq17910 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (M.op X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq16821 X0 X1
       grind)
    | exact superpose eq16821 eq17
    | (have j1 := eq16821 X0 X1
       grind)
    | exact resolve eq17 eq16821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq16821
  have eq18091 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17910 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17910
    | (have j0 := eq17910 X0 X1
       grind)
    | exact resolve eq17910 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17910
  have eq18823 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq18091 (σ X0) X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq18091
    | (have j0 := eq18091 (σ X0) X1
       grind)
    | exact resolve eq18091 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18091
  have eq19027 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq18823 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18823
    | (have j0 := eq18823 X0 X1
       grind)
    | exact resolve eq18823 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18823
  have eq19100 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19027 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19027
    | (have j0 := eq19027 X0 X1
       grind)
    | exact resolve eq19027 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19027
  have eq25879 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq5588
       have i₂ := eq19100 y x
       grind)
    | exact superpose eq19100 eq5588
    | (have j1 := eq19100 y x
       grind)
    | (have r₁ := eq5588
       have r₂ := eq19100 y x
       grind)
    | exact resolve eq5588 eq19100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25884 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq25879
  have eq25887 : (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have j1 := eq5621 y x
       grind)
    | (have r₁ := eq25884
       have r₂ := eq5621 x y
       grind)
    | exact resolve eq25884 eq5621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25884
  have eq31365 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq25887
       grind)
    | exact superpose eq25887 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq25887
       grind)
    | exact resolve eq12 eq25887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31366 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq25887
       grind)
    | exact superpose eq25887 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq25887
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq25887
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq25887
       grind)
    | exact resolve eq13 eq25887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31367 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq25887
       grind)
    | exact superpose eq25887 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq25887
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq25887
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq25887
       grind)
    | exact resolve eq13 eq25887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25887
  have eq31381 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq31367
  have eq31382 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq31366
  have eq31383 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq31381
       have r₂ := eq12 y x
       grind)
    | (have r₁ := eq31381
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq31381 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31381
  have eq31384 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq31365
       have r₂ := eq31382
       grind)
    | exact resolve eq31365 eq31382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31365 eq31382
  have eq32108 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq31383
       grind)
    | exact superpose eq31383 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq31383
       grind)
    | exact resolve eq12 eq31383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32109 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq31383
       grind)
    | exact superpose eq31383 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq31383
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq31383
       grind)
    | exact resolve eq13 eq31383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32110 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq31383
       grind)
    | exact superpose eq31383 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq31383
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq31383
       grind)
    | exact resolve eq13 eq31383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31383
  have eq32124 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq32110
  have eq32125 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq32124
  have eq32126 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by grind
  clear eq32109
  have eq32132 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq32125
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq32125 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32125
  have eq32133 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq32126
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq32126
    | exact resolve eq32126 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32126
  have eq32134 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq32108
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq32108
    | exact resolve eq32108 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32108
  have eq32139 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq32132
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq32132
    | exact resolve eq32132 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32132
  have eq32140 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq32134
       have r₂ := eq32133
       grind)
    | exact resolve eq32134 eq32133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32133 eq32134
  have eq32849 : (σ y) = (σ (k y x)) ∨ (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq32139
       have i₂ := eq32140
       grind)
    | exact superpose eq32140 eq32139
    | exact resolve eq32139 eq32140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32139 eq32140
  have eq32887 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k y x) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq32849
  have eq32932 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op x y) = (k y x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq32887
       grind)
    | exact superpose eq32887 eq16
    | exact resolve eq16 eq32887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32887
  have eq33024 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq31384
       grind)
    | exact superpose eq31384 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq31384
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq31384
       grind)
    | exact resolve eq13 eq31384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31384
  have eq33040 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x y) := by grind
  clear eq33024
  have eq33041 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x y) := by grind
  clear eq33040
  have eq33048 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq33041
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq33041 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33041
  have eq33055 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq33048
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq33048
    | exact resolve eq33048 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33048
  have eq33062 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33055
       grind)
    | exact superpose eq33055 eq16
    | exact resolve eq16 eq33055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33055
  have eq33123 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq33062
       have i₂ := eq19100 y x
       grind)
    | exact superpose eq19100 eq33062
    | (have j1 := eq19100 y x
       grind)
    | (have r₁ := eq33062
       have r₂ := eq19100 y x
       grind)
    | exact resolve eq33062 eq19100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19100 eq33062
  have eq33128 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq33123
  have eq34451 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq33128
       grind)
    | exact superpose eq33128 eq12
    | exact resolve eq12 eq33128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34452 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq33128
       grind)
    | exact superpose eq33128 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq33128
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq33128
       grind)
    | exact resolve eq13 eq33128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33128
  have eq34470 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq34452
  have eq34471 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq34470
  have eq34472 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq34451
  have eq34474 : (M.op x y) = (k x y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq34472
       have r₂ := eq34471
       grind)
    | exact resolve eq34472 eq34471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34471 eq34472
  have eq34478 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq32932
       have i₂ := eq34474
       grind)
    | exact superpose eq34474 eq32932
    | exact resolve eq32932 eq34474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32932 eq34474
  have eq34543 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq34478
  have eq34544 : (M.op x y) = (k y x) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq34543
  have eq34548 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq5588
       have i₂ := eq34544
       grind)
    | exact superpose eq34544 eq5588
    | exact resolve eq5588 eq34544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5588
  have eq34555 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq34548
  have eq34557 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq5621 y x
       grind)
    | (have r₁ := eq34555
       have r₂ := eq5621 x y
       grind)
    | exact resolve eq34555 eq5621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5621 eq34555
  have eq34881 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq34557
       grind)
    | exact superpose eq34557 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq34557
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq34557
       grind)
    | exact resolve eq13 eq34557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34557
  have eq34897 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq34881
  have eq34898 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq34897
  have eq34905 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq34898
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq34898 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34898
  have eq34912 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq34905
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq34905
    | exact resolve eq34905 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34905
  have eq34925 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34912
       grind)
    | exact superpose eq34912 eq16
    | exact resolve eq16 eq34912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34912
  have eq34984 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq34925
       have i₂ := eq34544
       grind)
    | exact superpose eq34544 eq34925
    | exact resolve eq34925 eq34544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34544
  have eq34995 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq34925
       have i₂ := eq6008 x y
       grind)
    | exact superpose eq6008 eq34925
    | (have j1 := eq6008 y x
       grind)
    | (have r₁ := eq34925
       have r₂ := eq6008 x y
       grind)
    | exact resolve eq34925 eq6008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6008
  have eq34996 : y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq34995
  have eq35004 : (σ y) = (σ (k y x)) := by grind
  clear eq34984
  have eq35020 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq34925
       have i₂ := eq35004
       grind)
    | exact superpose eq35004 eq34925
    | exact resolve eq34925 eq35004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34925
  have eq35028 : (k y x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq35004
       grind)
    | exact superpose eq35004 eq10
    | exact resolve eq10 eq35004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35004
  have eq35205 : y = (k y x) := by
    first
    | (have i₁ := eq35028
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq35028
    | exact resolve eq35028 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35028
  have eq38451 : (σ y) ≠ (σ y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq35020
       have i₂ := eq34996
       grind)
    | exact superpose eq34996 eq35020
    | exact resolve eq35020 eq34996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34996
  have eq38481 : (M.op x y) = (M.op y x) := by grind
  clear eq38451
  have eq38496 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq38481
       grind)
    | exact superpose eq38481 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq38481
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq38481
       grind)
    | exact resolve eq13 eq38481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38481
  have eq38513 : y = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq38496
  have eq38515 : (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq38513
       have r₂ := eq12 y x
       grind)
    | exact resolve eq38513 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38513
  have eq38517 : y = (M.op x y) := by
    first
    | (have i₁ := eq38515
       have i₂ := eq35205
       grind)
    | exact superpose eq35205 eq38515
    | exact resolve eq38515 eq35205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35205 eq38515
  have eq38533 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq35020
       have i₂ := eq38517
       grind)
    | exact superpose eq38517 eq35020
    | exact resolve eq35020 eq38517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35020 eq38517
  have eq38563 : False := by grind
  exact eq38563

/-- `Equation1437`: `x = (x ◇ x) ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_Equation1437 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1437 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1437.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
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
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq46 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq48 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq30 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq46 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq121 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq524 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq525 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq524 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq530 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq525 X0 X1
       have j1 := eq121 X0 X1
       grind)
    | (have r₁ := eq525 X0 X1
       have r₂ := eq121 X0 X1
       grind)
    | (have r₁ := eq525 X0 X0
       have r₂ := eq121 X0 X0
       grind)
    | exact resolve eq525 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq525
  have eq942 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq530 (σ X1) (σ X0)
       grind)
    | exact superpose eq530 eq15
    | exact resolve eq15 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq945 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq942 X0 X1
       have i₂ := eq530 X1 X0
       grind)
    | exact superpose eq530 eq942
    | exact resolve eq942 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq942
  have eq949 : False := by grind
  exact eq949

/-- `Equation1443`: `x = (x ◇ y) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_pxx_pxy_Equation1443 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1443.models_iff G M).mp hM
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq61 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) (M.op (M.op X0 X1) X3))) := by
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
  have eq66 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1 (M.op X0 (M.op X0 x))
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq311 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq312 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq311 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq314 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq312 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq312 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq312 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq329 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq314 (σ X0)
       grind)
    | exact superpose eq314 eq15
    | exact resolve eq15 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq329 X0
       have i₂ := eq314 X0
       grind)
    | exact superpose eq314 eq329
    | exact resolve eq329 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314 eq329
  have eq395 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq348 X0
       grind)
    | exact superpose eq348 eq9
    | exact resolve eq9 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq348 X0
       grind)
    | exact superpose eq348 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq398 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq348 X0
       grind)
    | exact superpose eq348 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq397 X0 X1
       have j1 := eq398 X0 X1
       grind)
    | (have r₁ := eq397 X0 X1
       have r₂ := eq398 X0 X1
       grind)
    | exact resolve eq397 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq398
  have eq510 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq399 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq399
    | exact resolve eq399 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq399 X1 (σ X0)
       grind)
    | exact superpose eq399 eq15
    | (have j1 := eq399 X1 (σ X0)
       grind)
    | exact resolve eq15 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq550 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq510 (τ X1) X0
       grind)
    | exact superpose eq510 eq18
    | (have j1 := eq510 (τ X1) X0
       grind)
    | exact resolve eq18 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq510
  have eq881 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq550 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq550
    | exact resolve eq550 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq933 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq881 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq881
    | (have j0 := eq881 X0 X1
       grind)
    | exact resolve eq881 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq1135 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq521 x y
       grind)
    | exact superpose eq521 eq16
    | (have j1 := eq521 x y
       grind)
    | exact resolve eq16 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq1310 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1135
       have i₂ := eq933 y x
       grind)
    | exact superpose eq933 eq1135
    | (have j1 := eq933 (σ y) (σ x)
       grind)
    | (have r₁ := eq1135
       have r₂ := eq933 y x
       grind)
    | exact resolve eq1135 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933 eq1135
  have eq1311 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1310
  have eq1316 : x = (M.op x (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66 x y
       have i₂ := eq1311
       grind)
    | exact superpose eq1311 eq66
    | exact resolve eq66 eq1311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1319 : ∀ X0 : G, x = (M.op x (M.op x (M.op x X0))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq1311
       grind)
    | exact superpose eq1311 eq9
    | exact resolve eq9 eq1311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311
  have eq1381 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1319 x
       have i₂ := eq1316
       grind)
    | exact superpose eq1316 eq1319
    | exact resolve eq1319 eq1316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316 eq1319
  have eq1390 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1381
  have eq1397 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1390
       grind)
    | exact superpose eq1390 eq16
    | exact resolve eq16 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1402 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq66 (σ x) (σ y)
       have i₂ := eq1390
       grind)
    | exact superpose eq1390 eq66
    | exact resolve eq66 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390
  have eq1408 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1402
       have i₂ := eq348 x
       grind)
    | exact superpose eq348 eq1402
    | exact resolve eq1402 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402
  have eq1422 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq395 x (σ (M.op x x))
       have i₂ := eq1408
       grind)
    | exact superpose eq1408 eq395
    | exact resolve eq395 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408
  have eq1434 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1422
       have i₂ := eq348 x
       grind)
    | exact superpose eq348 eq1422
    | exact resolve eq1422 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422
  have eq1454 : x = (M.op x (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq66 x x
       have i₂ := eq1434
       grind)
    | exact superpose eq1434 eq66
    | exact resolve eq66 eq1434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1703 : ∀ X0 : G, x = (M.op (M.op x X0) x) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 x
       have i₂ := eq1454
       grind)
    | exact superpose eq1454 eq9
    | exact resolve eq9 eq1454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454
  have eq1734 : ∀ X0 : G, (σ x) = (σ (M.op x x)) ∨ (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq66 x X0
       have i₂ := eq1703 X0
       grind)
    | exact superpose eq1703 eq66
    | exact resolve eq66 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1703
  have eq1777 : ∀ X0 : G, (M.op x x) = (τ (σ x)) ∨ (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1734 X0
       grind)
    | exact superpose eq1734 eq10
    | (have j1 := eq1734 X0
       grind)
    | exact resolve eq10 eq1734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734
  have eq1829 : ∀ X0 : G, x = (M.op x x) ∨ (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq1777 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1777
    | (have j0 := eq1777 X0
       grind)
    | exact resolve eq1777 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1777
  have eq1852 : ∀ X0 : G, x = (M.op x (M.op x x)) ∨ (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq66 x x
       have i₂ := eq1829 X0
       grind)
    | exact superpose eq1829 eq66
    | (have j1 := eq1829 X0
       grind)
    | exact resolve eq66 eq1829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1829
  have eq1884 : ∀ X0 X1 : G, x = (M.op (M.op x X0) x) ∨ (M.op x x) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x X0 x
       have i₂ := eq1852 X1
       grind)
    | exact superpose eq1852 eq9
    | (have j1 := eq1852 X1
       grind)
    | exact resolve eq9 eq1852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1852
  have eq1979 : ∀ X0 X1 : G, (M.op x x) = (M.op x X0) ∨ (M.op x x) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq66 x X0
       have i₂ := eq1884 X0 X1
       grind)
    | exact superpose eq1884 eq66
    | (have j1 := eq1884 X0 X0
       grind)
    | exact resolve eq66 eq1884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1884
  have eq2055 : ∀ X0 : G, (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq1979 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1979
  have eq2056 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq2055 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2055
  have eq2111 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1397
       have i₂ := eq2056 y
       grind)
    | exact superpose eq2056 eq1397
    | exact resolve eq1397 eq2056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397
  have eq2129 : x = (M.op x x) := by
    first
    | (have r₁ := eq2111
       have r₂ := eq1434
       grind)
    | exact resolve eq2111 eq1434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1434 eq2111
  have eq2143 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq2056 X0
       have i₂ := eq2129
       grind)
    | exact superpose eq2129 eq2056
    | exact resolve eq2056 eq2129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2149 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq395 x X0
       have i₂ := eq2129
       grind)
    | exact superpose eq2129 eq395
    | exact resolve eq395 eq2129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq2129
  have eq2173 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq2149 X0
       have i₂ := eq348 x
       grind)
    | exact superpose eq348 eq2149
    | exact resolve eq2149 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2149
  have eq2180 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2173 X0
       have i₂ := eq2143 x
       grind)
    | exact superpose eq2143 eq2173
    | exact resolve eq2173 eq2143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2173
  have eq2760 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq66 (σ x) X0
       have i₂ := eq2180 X0
       grind)
    | exact superpose eq2180 eq66
    | exact resolve eq66 eq2180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq2180
  have eq2772 : ∀ X0 : G, (σ (M.op x x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq2760 X0
       have i₂ := eq348 x
       grind)
    | exact superpose eq348 eq2760
    | exact resolve eq2760 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348 eq2760
  have eq2781 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq2772 X0
       have i₂ := eq2143 x
       grind)
    | exact superpose eq2143 eq2772
    | exact resolve eq2772 eq2143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2772
  have eq2801 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2781 (σ y)
       grind)
    | exact superpose eq2781 eq16
    | exact resolve eq16 eq2781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2781
  have eq2846 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2801
       have i₂ := eq2056 y
       grind)
    | exact superpose eq2056 eq2801
    | exact resolve eq2801 eq2056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2056 eq2801
  have eq2862 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2846
       have i₂ := eq2143 x
       grind)
    | exact superpose eq2143 eq2846
    | exact resolve eq2846 eq2143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143 eq2846
  have eq2863 : False := by grind
  exact eq2863

/-- `Equation1445`: `x = (x ◇ y) ◇ (x ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation1445 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1445 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1445.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq268 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq268 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq271 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq269 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq269 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq269 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq282 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq271 (σ X0)
       grind)
    | exact superpose eq271 eq15
    | exact resolve eq15 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq282 X0
       have i₂ := eq271 X0
       grind)
    | exact superpose eq271 eq282
    | exact resolve eq282 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq282
  have eq346 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq301 X0
       grind)
    | exact superpose eq301 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq301 X0
       grind)
    | exact superpose eq301 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq349 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq346 X0 X1
       have j1 := eq347 X0 X1
       grind)
    | (have r₁ := eq346 X0 X1
       have r₂ := eq347 X0 X1
       grind)
    | exact resolve eq346 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq347
  have eq426 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq349 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq349
    | exact resolve eq349 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq349 X1 X0
       grind)
    | exact superpose eq349 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq349 X1 (σ X1)
       grind)
    | (have r₁ := eq13 X1 (σ X0)
       have r₂ := eq349 X0 X1
       grind)
    | exact resolve eq13 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq447 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq440 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq451 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq447 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq447 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq447 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq511 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq451 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq451
    | exact resolve eq451 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq511 (τ X0) X1
       grind)
    | exact superpose eq511 eq18
    | (have j1 := eq511 (τ X0) X1
       grind)
    | exact resolve eq18 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq579 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq511 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq1039 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq562 X1 (τ X0)
       grind)
    | exact superpose eq562 eq17
    | (have j1 := eq562 X1 (τ X0)
       grind)
    | exact resolve eq17 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq562
  have eq1048 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1039 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1039
    | (have j0 := eq1039 X0 X1
       grind)
    | exact resolve eq1039 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq1059 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1048 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1048
    | (have j0 := eq1048 X0 X1
       grind)
    | exact resolve eq1048 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq1060 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1059 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1059
    | (have j0 := eq1059 X0 X1
       grind)
    | exact resolve eq1059 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059
  have eq1116 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1060 X1 X0
       have i₂ := eq426 X0 X1
       grind)
    | exact superpose eq426 eq1060
    | (have j1 := eq426 X0 X1
       grind)
    | exact resolve eq1060 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1117 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1060 X0 (σ X1)
       have i₂ := eq451 X0 X1
       grind)
    | exact superpose eq451 eq1060
    | (have j0 := eq1060 X1 (σ X0)
       have j1 := eq451 X1 X0
       grind)
    | exact resolve eq1060 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451 eq1060
  have eq1155 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1116 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1182 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1117 X0 X1
       have j1 := eq579 X1 (σ X0)
       grind)
    | (have r₁ := eq1117 X0 X0
       have r₂ := eq579 X0 (σ X0)
       grind)
    | exact resolve eq1117 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579 eq1117
  have eq1200 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1182 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1182
    | (have j0 := eq1182 X0 X1
       grind)
    | exact resolve eq1182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq1273 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1155 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1155
    | (have j0 := eq1155 (σ X0) X1
       grind)
    | exact resolve eq1155 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155
  have eq1943 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq1200 X1 (σ X0)
       grind)
    | exact superpose eq1200 eq28
    | (have j1 := eq1200 X1 (σ X0)
       grind)
    | exact resolve eq28 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1200
  have eq1957 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1943 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1943
    | (have j0 := eq1943 X0 X1
       grind)
    | exact resolve eq1943 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1943
  have eq1968 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1957 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1957
    | (have j0 := eq1957 X0 X1
       grind)
    | exact resolve eq1957 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957
  have eq1975 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1968 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1968
    | (have j0 := eq1968 X0 X1
       grind)
    | exact resolve eq1968 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1968
  have eq2084 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1975 y x
       grind)
    | exact superpose eq1975 eq16
    | (have j1 := eq1975 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq1975 y x
       grind)
    | exact resolve eq16 eq1975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1975
  have eq2111 : y = (k y x) := by grind
  clear eq2084
  have eq2135 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq426 x y
       have i₂ := eq2111
       grind)
    | exact superpose eq2111 eq426
    | (have j0 := eq426 x y
       grind)
    | exact resolve eq426 eq2111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426 eq2111
  have eq2138 : y = (M.op x y) := by grind
  clear eq2135
  have eq2313 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x (τ (σ y)))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1273 x (σ y)
       grind)
    | exact superpose eq1273 eq16
    | (have j1 := eq1273 x (σ y)
       grind)
    | exact resolve eq16 eq1273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273
  have eq2372 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x (τ (σ y)))) := by
    first
    | (have i₁ := eq2313
       have i₂ := eq2138
       grind)
    | exact superpose eq2138 eq2313
    | exact resolve eq2313 eq2138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2138 eq2313
  have eq2373 : (M.op (σ x) (σ y)) = (σ (M.op x (τ (σ y)))) := by grind
  clear eq2372
  have eq2381 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2373
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2373
    | exact resolve eq2373 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2373
  have eq2384 : False := by grind
  exact eq2384

/-- `Equation1445`: `x = (x ◇ y) ◇ (x ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation1445 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1445 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1445.models_iff G M).mp hM
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq152 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
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
  have eq153 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq867 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (τ X1)
       have i₂ := eq152 X0 X1
       grind)
    | exact superpose eq152 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq152 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq152 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) X1
       have r₂ := eq152 (M.op (τ X1) X1) X1
       grind)
    | exact resolve eq13 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq872 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq867 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq873 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq872 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq2234 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq873 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq873
    | exact resolve eq873 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq2277 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2234 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2234
    | (have j0 := eq2234 X0 X1
       grind)
    | exact resolve eq2234 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2234
  have eq2312 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq2277 X1 X0
       grind)
    | exact superpose eq2277 eq10
    | (have j1 := eq2277 X1 X0
       grind)
    | exact resolve eq10 eq2277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2354 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2312 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2312
    | (have j0 := eq2312 X0 X1
       grind)
    | exact resolve eq2312 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2312
  have eq2366 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq2354 X0 (σ X1)
       grind)
    | exact superpose eq2354 eq28
    | (have j1 := eq2354 X0 (σ X1)
       grind)
    | exact resolve eq28 eq2354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2354
  have eq3450 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq153 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq4290 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq2366 (σ X0) X1
       grind)
    | exact superpose eq2366 eq37
    | (have j1 := eq2366 (σ X0) X1
       grind)
    | exact resolve eq37 eq2366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2366
  have eq4355 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4290 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4290
    | (have j0 := eq4290 X0 X1
       grind)
    | exact resolve eq4290 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4290
  have eq4387 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4355 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4355
    | (have j0 := eq4355 X0 X1
       grind)
    | exact resolve eq4355 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4355
  have eq4397 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4387 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4387
    | (have j0 := eq4387 X0 X1
       grind)
    | exact resolve eq4387 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4387
  have eq4601 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4397 X0 X1
       grind)
    | exact superpose eq4397 eq11
    | (have j1 := eq4397 X0 X1
       grind)
    | exact resolve eq11 eq4397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4397
  have eq5482 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4601 x y
       grind)
    | exact superpose eq4601 eq16
    | (have j1 := eq4601 x y
       grind)
    | exact resolve eq16 eq4601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4601
  have eq5520 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5482
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq5482
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq5482
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5482
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5482 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5521 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq5482
       have i₂ := eq2277 y x
       grind)
    | exact superpose eq2277 eq5482
    | (have j1 := eq2277 y x
       grind)
    | (have r₁ := eq5482
       have r₂ := eq2277 y x
       grind)
    | (have r₁ := eq5482
       have r₂ := eq2277 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5482
       have r₂ := eq2277 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5482 eq2277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2277 eq5482
  have eq5524 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5521
  have eq5525 : x = y ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq5524
  have eq5526 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5520
  have eq5527 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq5526
  have eq5531 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5525
       grind)
    | exact superpose eq5525 eq16
    | exact resolve eq16 eq5525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5525
  have eq5532 : x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5531
       have r₂ := eq22 x
       grind)
    | exact resolve eq5531 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5531
  have eq5538 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3450 x y
       have i₂ := eq5532
       grind)
    | exact superpose eq5532 eq3450
    | (have j0 := eq3450 x y
       grind)
    | exact resolve eq3450 eq5532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3450 eq5532
  have eq5543 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5538
  have eq5544 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5543
  have eq5548 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5527
       grind)
    | exact superpose eq5527 eq16
    | exact resolve eq16 eq5527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5527
  have eq5549 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5548
       have r₂ := eq22 x
       grind)
    | exact resolve eq5548 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5548
  have eq5558 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5544
       grind)
    | exact superpose eq5544 eq16
    | exact resolve eq16 eq5544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5544
  have eq5579 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5558
       have i₂ := eq5549
       grind)
    | exact superpose eq5549 eq5558
    | exact resolve eq5558 eq5549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5549 eq5558
  have eq5580 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq5579
  have eq5581 : (σ x) = (σ y) := by grind
  clear eq5580
  have eq5582 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5581
       grind)
    | exact superpose eq5581 eq16
    | exact resolve eq16 eq5581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5583 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5581
       grind)
    | exact superpose eq5581 eq10
    | exact resolve eq10 eq5581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5581
  have eq5639 : x = y := by
    first
    | (have i₁ := eq5583
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5583
    | exact resolve eq5583 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5583
  have eq5640 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5582
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5582
    | exact resolve eq5582 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5582
  have eq5641 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5640
       have i₂ := eq5639
       grind)
    | exact superpose eq5639 eq5640
    | exact resolve eq5640 eq5639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5639 eq5640
  have eq5642 : False := by grind
  exact eq5642

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_y_pxy_y_pxy_Equation1446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X2))) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq176 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq196 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq183
       grind)
    | exact superpose eq183 eq41
    | exact resolve eq41 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq183
  have eq197 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq196
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq196
    | exact resolve eq196 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq196
  have eq199 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq197
    | exact resolve eq197 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq203 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq199 eq184
    | exact resolve eq184 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq203
       have r₂ := eq27
       grind)
    | exact resolve eq203 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq208 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq206 eq27
    | exact resolve eq27 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) (M.op (σ y) X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq206 eq176
    | exact resolve eq176 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq232 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq223 eq223
    | exact resolve eq223 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by grind
  clear eq232
  have eq257 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) (M.op (M.op (σ x) (σ x)) X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq241 eq16
    | exact resolve eq16 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq281 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq257 eq223
    | exact resolve eq223 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223 eq257
  have eq287 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq281
  have eq480 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq287 eq13
    | exact resolve eq13 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq484 : ∀ X0 : G, (σ x) ≠ (M.op (σ y) X0) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq287 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | exact resolve eq13 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq485 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq480
  have eq522 : y ≠ (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ y = (k x y) := by
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
  have eq524 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq524
       have i₂ := eq485 sF3
       grind)
    | exact superpose eq485 eq524
    | exact resolve eq524 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq545 : y ≠ (M.op x y) ∨ (k y y) = (M.op y x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq522
       have i₂ := eq485 y
       grind)
    | exact superpose eq485 eq522
    | exact resolve eq522 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq8517 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq206 eq543
    | (have r₁ := eq543
       have r₂ := eq206
       grind)
    | exact resolve eq543 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq543
  have eq8518 : (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq8517
  have eq8519 : (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq199 eq8518
    | exact resolve eq8518 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8518
  have eq8520 : (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq8519
       have r₂ := eq208
       grind)
    | exact resolve eq8519 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq8519
  have eq8521 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq486 eq8520
    | exact resolve eq8520 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486 eq8520
  have eq8556 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8521 eq484
    | (have j0 := eq484 (σ x)
       grind)
    | (have r₁ := eq484 (σ x)
       have r₂ := eq8521
       grind)
    | exact resolve eq484 eq8521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484 eq8521
  have eq8631 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq8556
  have eq8632 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq8631
  have eq8691 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq8632
    | exact resolve eq8632 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq8632
  have eq8723 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq199 eq8691
    | exact resolve eq8691 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq8691
  have eq8739 : y = (M.op x y) := by
    first
    | (have r₁ := eq8723
       have r₂ := eq27
       grind)
    | exact resolve eq8723 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8723
  have eq8747 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq8739
       grind)
    | exact superpose eq8739 eq18
    | exact resolve eq18 eq8739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq8748 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq8739
       grind)
    | exact superpose eq8739 eq24
    | exact resolve eq24 eq8739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq8752 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | (have i₁ := eq545
       have i₂ := eq8739
       grind)
    | exact superpose eq8739 eq545
    | (have r₁ := eq545
       have r₂ := eq8739
       grind)
    | exact resolve eq545 eq8739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545 eq8739
  have eq8753 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (k x (M.op x y)) := by grind
  clear eq8752
  have eq8755 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq8748 eq20
    | exact resolve eq20 eq8748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8748
  have eq9817 : (k (M.op x y) (M.op x y)) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k x (M.op x y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq8753 eq13
    | (have j0 := eq13 x (M.op x y)
       grind)
    | exact resolve eq13 eq8753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8753
  have eq9827 : (k x (M.op x y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | (have r₁ := eq9817
       have r₂ := eq485 (M.op x y)
       grind)
    | exact resolve eq9817 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485 eq9817
  have eq9832 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq8747 eq9827
    | exact resolve eq9827 eq8747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8747 eq9827
  have eq9833 : (M.op x y) = (k x (M.op x y)) := by grind
  clear eq9832
  have eq10424 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq9833 eq36
    | exact resolve eq36 eq9833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq9833
  have eq10433 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10424
    | exact resolve eq10424 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq10424
  have eq10436 : (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq8755 eq10433
    | exact resolve eq10433 eq8755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10433
  have eq10443 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10436 eq184
    | exact resolve eq184 eq10436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq10436
  have eq10455 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10443
  have eq10462 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq10455 eq27
    | exact resolve eq27 eq10455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq10455
  have eq10464 : False := by grind
  exact eq10464
