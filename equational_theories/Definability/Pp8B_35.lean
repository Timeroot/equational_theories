import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pyy_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq267 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq267 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq267 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq267 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq279 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq268 (σ X0)
       grind)
    | exact superpose eq268 eq15
    | exact resolve eq15 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq268 (τ X0)
       grind)
    | exact superpose eq268 eq31
    | exact resolve eq31 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq292 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq285 X0
       have i₂ := eq268 X0
       grind)
    | exact superpose eq268 eq285
    | exact resolve eq285 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq298 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq279 X0
       have i₂ := eq268 X0
       grind)
    | exact superpose eq268 eq279
    | exact resolve eq279 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq279
  have eq417 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq434 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq417 X0 X1
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq417
    | (have j0 := eq417 X0 X1
       grind)
    | exact resolve eq417 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq834 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq434 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq434
    | exact resolve eq434 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq877 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq834 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq834
    | (have j0 := eq834 X0 X1
       grind)
    | exact resolve eq834 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq834
  have eq880 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq877 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq877 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq877 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq881 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq880 X0 X1
       have i₂ := eq292 X0
       grind)
    | exact superpose eq292 eq880
    | (have j0 := eq880 X0 X1
       grind)
    | exact resolve eq880 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292 eq880
  have eq882 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq881 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq881
    | (have j0 := eq881 X0 X1
       grind)
    | exact resolve eq881 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq883 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq882 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq882
    | exact resolve eq882 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq894 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq882 (σ X0) X1
       grind)
    | exact superpose eq882 eq15
    | (have j1 := eq882 (σ X0) X1
       grind)
    | exact resolve eq15 eq882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq926 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq894 X0 X1
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq894
    | (have j0 := eq894 X0 X1
       grind)
    | exact resolve eq894 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq964 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq883 (τ X1) X0
       grind)
    | exact superpose eq883 eq17
    | (have j1 := eq883 (τ X1) X0
       grind)
    | exact resolve eq17 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq883
  have eq1146 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq964 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq964
    | exact resolve eq964 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq1194 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1146 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1146
    | (have j0 := eq1146 X0 X1
       grind)
    | exact resolve eq1146 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146
  have eq2483 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq926 x y
       grind)
    | exact superpose eq926 eq16
    | (have j1 := eq926 x y
       grind)
    | exact resolve eq16 eq926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2501 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq926 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq2530 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2483
       have i₂ := eq1194 y x
       grind)
    | exact superpose eq1194 eq2483
    | (have j1 := eq1194 y x
       grind)
    | (have r₁ := eq2483
       have r₂ := eq1194 y x
       grind)
    | exact resolve eq2483 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2483
  have eq2531 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2530
  have eq2536 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2531
       grind)
    | exact superpose eq2531 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2531
       grind)
    | exact resolve eq13 eq2531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2538 : x ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq2531
       grind)
    | exact superpose eq2531 eq12
    | (have j0 := eq12 x x
       grind)
    | exact resolve eq12 eq2531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2531
  have eq2540 : x = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2536
  have eq2541 : (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq2540
       have r₂ := eq2538
       grind)
    | exact resolve eq2540 eq2538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2538 eq2540
  have eq2566 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2501 x y
       have i₂ := eq2541
       grind)
    | exact superpose eq2541 eq2501
    | (have j0 := eq2501 x y
       grind)
    | exact resolve eq2501 eq2541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2501 eq2541
  have eq2589 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2566
  have eq2590 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2589
  have eq2674 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2590
       grind)
    | exact superpose eq2590 eq16
    | exact resolve eq16 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2679 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq2590
       grind)
    | exact superpose eq2590 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2681 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq2590
       grind)
    | exact superpose eq2590 eq12
    | exact resolve eq12 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2590
  have eq2683 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2681
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2681
    | exact resolve eq2681 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2681
  have eq2685 : (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq2679
       have r₂ := eq298 x
       grind)
    | exact resolve eq2679 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2679
  have eq2687 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2685
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2685
    | exact resolve eq2685 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2685
  have eq2688 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2687
       have i₂ := eq298 x
       grind)
    | exact superpose eq298 eq2687
    | exact resolve eq2687 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298 eq2687
  have eq2689 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq2688
       have r₂ := eq2683
       grind)
    | exact resolve eq2688 eq2683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2683 eq2688
  have eq2697 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1194 y x
       have i₂ := eq2689
       grind)
    | exact superpose eq2689 eq1194
    | (have j0 := eq1194 y x
       grind)
    | exact resolve eq1194 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194 eq2689
  have eq2745 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq2697
       have r₂ := eq2674
       grind)
    | exact resolve eq2697 eq2674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2697
  have eq2762 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2674
       have i₂ := eq2745
       grind)
    | exact superpose eq2745 eq2674
    | exact resolve eq2674 eq2745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2674 eq2745
  have eq2770 : False := by grind
  exact eq2770

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation2300 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  have eq69 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq71 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq69
       grind)
    | exact superpose eq69 eq16
    | exact resolve eq16 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq71 x y
       grind)
    | exact superpose eq71 eq44
    | (have j1 := eq71 x y
       grind)
    | exact resolve eq44 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq100
    | exact resolve eq100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
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
  have eq109 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op y y) ∨ (k x y) = (M.op x x) := by
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
  have eq110 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq111 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq111 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq111 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq115 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq112 x
       grind)
    | exact superpose eq112 eq43
    | exact resolve eq43 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq116 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq112 y
       grind)
    | exact superpose eq112 eq69
    | exact resolve eq69 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq118 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq81
       have i₂ := eq112 sF3
       grind)
    | exact superpose eq112 eq81
    | exact resolve eq81 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq119 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq118
       have i₂ := eq112 y
       grind)
    | exact superpose eq112 eq118
    | exact resolve eq118 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq121 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq112 sF3
       grind)
    | exact superpose eq112 eq116
    | exact resolve eq116 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq122 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq115
       have i₂ := eq112 sF2
       grind)
    | exact superpose eq112 eq115
    | exact resolve eq115 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq115
  have eq846 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq103 eq71
    | (have j0 := eq71 (σ x) (σ y)
       grind)
    | exact resolve eq71 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq847 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq846
    | exact resolve eq846 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq850 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq847
       have r₂ := eq27
       grind)
    | exact resolve eq847 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq852 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq850
    | exact resolve eq850 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq854 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq852 eq110
    | (have r₁ := eq110
       have r₂ := eq852
       grind)
    | exact resolve eq110 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq852
  have eq863 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq854
  have eq884 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq863 eq103
    | exact resolve eq103 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq863
  have eq887 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq884
  have eq889 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq887
       have r₂ := eq27
       grind)
    | exact resolve eq887 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq891 : (τ (σ y)) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq889 eq119
    | exact resolve eq119 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq889
  have eq899 : (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq891
    | exact resolve eq891 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq891
  have eq905 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y y) ∨ (M.op x y) = (k x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq109
       have i₂ := eq899
       grind)
    | exact superpose eq899 eq109
    | (have r₁ := eq109
       have r₂ := eq899
       grind)
    | exact resolve eq109 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq906 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq122
       have i₂ := eq899
       grind)
    | exact superpose eq899 eq122
    | exact resolve eq122 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq899
  have eq914 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
  clear eq905
  have eq915 : (M.op x y) = (k x y) ∨ y = (M.op y y) := by grind
  clear eq914
  have eq917 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq906
    | exact resolve eq906 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq919 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq915
       grind)
    | exact superpose eq915 eq44
    | exact resolve eq44 eq915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq921 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq919
    | exact resolve eq919 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq939 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq921 eq71
    | (have j0 := eq71 (σ x) (σ y)
       grind)
    | exact resolve eq71 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq921
  have eq940 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq939
    | exact resolve eq939 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939
  have eq943 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq940
       have r₂ := eq27
       grind)
    | exact resolve eq940 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq945 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq943
    | exact resolve eq943 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq948 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq945 eq917
    | exact resolve eq917 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917 eq945
  have eq959 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq948
  have eq962 : y = (M.op y y) := by
    first
    | (have r₁ := eq959
       have r₂ := eq27
       grind)
    | exact resolve eq959 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq965 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq121
       have i₂ := eq962
       grind)
    | exact superpose eq962 eq121
    | exact resolve eq121 eq962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq970 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq962
       grind)
    | exact superpose eq962 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq962
       grind)
    | exact resolve eq13 eq962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq971 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq970 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq975 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq965
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq965
    | exact resolve eq965 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq965
  have eq986 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq975 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq975
       grind)
    | exact resolve eq13 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq987 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq986 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq1056 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq971 x
       grind)
    | exact superpose eq971 eq44
    | exact resolve eq44 eq971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq971
  have eq1065 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1056
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1056
    | exact resolve eq1056 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1056
  have eq1066 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1065
    | exact resolve eq1065 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1065
  have eq1180 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq987 eq1066
    | exact resolve eq1066 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987 eq1066
  have eq1194 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1180
    | exact resolve eq1180 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1180
  have eq1203 : False := by grind
  exact eq1203

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation2300 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X0))) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq36 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq22
    | exact resolve eq22 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq97 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq98 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (τ (M.op X1 X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X1
       have i₂ := eq68 X1
       grind)
    | exact superpose eq68 eq97
    | (have j0 := eq97 X0 X1
       grind)
    | exact resolve eq97 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq100 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq95
    | (have j0 := eq95 X0 X1
       grind)
    | exact resolve eq95 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq197 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X0 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq208 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq197 X0 X1 X2
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq197
    | (have j0 := eq197 X0 X1 X2
       grind)
    | exact resolve eq197 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq197
  have eq1641 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op (τ X0) (M.op X1 (τ X0)))))) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (M.op X1 (M.op (τ X0) (M.op X1 (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq98 (M.op X1 (M.op (τ X1) (M.op X1 (τ X1)))) X1
       have i₂ := eq9 (τ X1) X1
       grind)
    | exact superpose eq9 eq98
    | (have j0 := eq98 (τ (M.op X0 X0)) X0
       grind)
    | exact resolve eq98 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq1682 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op (τ X0) (M.op X1 (τ X0)))) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (σ (M.op X1 (M.op (τ X0) (M.op X1 (τ X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1641 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1641
    | (have j0 := eq1641 X0 X1
       grind)
    | exact resolve eq1641 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1641
  have eq4896 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) (k (σ X1) X2)) ≠ (M.op X3 (k (σ X1) X2)) ∨ (k (k (σ X1) X2) X3) = (M.op (σ X0) (k (σ X1) X2)) ∨ (k (σ X1) X2) = X3 ∨ (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (k (σ X0) X1) X1
       have i₂ := eq208 X0 X1 X2
       grind)
    | exact superpose eq208 eq13
    | (have j0 := eq13 (k (k (σ X1) X2) X3) (M.op (σ X0) (k (σ X1) X2))
       have j1 := eq208 X1 X2 X0
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq208 X0 X1 X2
       grind)
    | exact resolve eq13 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq70500 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (σ (M.op X1 (M.op (τ X0) (M.op X1 (τ X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1
       have i₂ := eq1682 X0 X1
       grind)
    | exact superpose eq1682 eq9
    | (have j1 := eq1682 X0 X1
       grind)
    | exact resolve eq9 eq1682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1682
  have eq70544 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (σ (M.op X1 (M.op (τ X0) (M.op X1 (τ X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq70500 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq70500
    | (have j0 := eq70500 X0 X1
       grind)
    | exact resolve eq70500 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq70500
  have eq70545 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (σ (M.op X1 (M.op (τ X0) (M.op X1 (τ X0)))))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq70544 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70544
  have eq70652 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (k (σ X0) (σ (M.op X1 (M.op (τ (σ X0)) (M.op X1 (τ (σ X0))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq70545 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq70545
    | (have j0 := eq70545 (σ X0) X1
       grind)
    | exact resolve eq70545 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70545
  have eq70943 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ X0) = (k (σ X0) (σ (M.op X1 (M.op (τ (σ X0)) (M.op X1 (τ (σ X0))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq70652 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq70652
    | (have j0 := eq70652 X0 X1
       grind)
    | exact resolve eq70652 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70652
  have eq70955 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ X0) = (k (σ X0) (σ (M.op X1 (M.op (τ (σ X0)) (M.op X1 (τ (σ X0))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq70943 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq70943
    | (have j0 := eq70943 X0 X1
       grind)
    | exact resolve eq70943 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70943
  have eq70963 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op X1 (M.op (τ (σ X0)) (M.op X1 (τ (σ X0))))))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq70955 X0 X1
       have i₂ := eq15 X0 (M.op X1 (M.op (τ (σ X0)) (M.op X1 (τ (σ X0)))))
       grind)
    | exact superpose eq15 eq70955
    | (have j0 := eq70955 X0 X1
       grind)
    | exact resolve eq70955 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70955
  have eq70964 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ X0) = (σ (k X0 (M.op X1 (M.op X0 (M.op X1 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq70963 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq70963
    | (have j0 := eq70963 X0 X1
       grind)
    | exact resolve eq70963 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70963
  have eq224762 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4896 X2 X0 X1 (σ X2)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4896
  have eq224763 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq224762 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224762
  have eq224772 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq224763 X0 X1 X2
       have i₂ := eq36 X0 X1 X2
       grind)
    | exact superpose eq36 eq224763
    | (have j0 := eq224763 X0 X1 X2
       grind)
    | exact resolve eq224763 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq224763
  have eq224773 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq224772 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224772
  have eq225327 : ∀ X0 X1 X2 : G, (k (σ (k X1 (τ X2))) X0) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X0 (k X1 (τ X2))
       have i₂ := eq224773 X1 X2 (τ X0)
       grind)
    | exact superpose eq224773 eq19
    | (have j1 := eq224773 X1 X2 (τ X0)
       grind)
    | exact resolve eq19 eq224773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224773
  have eq225650 : ∀ X0 X1 X2 : G, (k (σ (k X1 (τ X2))) X0) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq225327 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq225327
    | (have j0 := eq225327 X0 X1 X2
       grind)
    | exact resolve eq225327 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225327
  have eq225800 : ∀ X0 X1 X2 : G, (k (k (σ X1) X2) X0) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq225650 X0 X1 X2
       have i₂ := eq19 X2 X1
       grind)
    | exact superpose eq19 eq225650
    | (have j0 := eq225650 X0 X1 X2
       grind)
    | exact resolve eq225650 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225650
  have eq225930 : ∀ X0 X1 X2 : G, (k (k (σ X1) X2) X0) = (M.op X0 (k (σ X1) X2)) ∨ (k (σ X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq225800 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq225800
    | (have j0 := eq225800 X0 X1 X2
       grind)
    | exact resolve eq225800 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225800
  have eq226165 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (M.op X2 (k X0 X1)) ∨ (k X0 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq225930 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq225930
    | exact resolve eq225930 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225930
  have eq228192 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq228801 : ∀ X0 X1 X2 : G, (σ X0) = (σ (k X0 (M.op X2 (M.op X0 (M.op X2 X0))))) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq228192 X0 X1
       have i₂ := eq70964 X0 X1
       grind)
    | exact superpose eq70964 eq228192
    | (have j1 := eq70964 X0 X2
       grind)
    | exact resolve eq228192 eq70964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70964 eq228192
  have eq450036 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (M.op X1 (M.op X0 (M.op X1 X0)))) ∨ X0 = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k X0 (M.op X1 (M.op X0 (M.op X1 X0))))
       have i₂ := eq228801 X0 X2 X1
       grind)
    | exact superpose eq228801 eq10
    | (have j1 := eq228801 X0 X2 X2
       grind)
    | exact resolve eq10 eq228801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228801
  have eq450520 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X0 (M.op X1 X0)))) = X0 ∨ X0 = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq450036 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq450036
    | (have j0 := eq450036 X0 X1 X2
       grind)
    | exact resolve eq450036 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450036
  have eq453340 : ∀ X0 X2 X3 : G, (k X0 X2) = (M.op X2 X0) ∨ X0 = X2 ∨ X0 = X3 ∨ (k X0 X3) = (M.op X3 X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq226165 X0 (M.op x (M.op X0 (M.op x X0))) X2
       have i₂ := eq450520 X0 x X2
       grind)
    | exact superpose eq450520 eq226165
    | (have j0 := eq226165 X0 X2 (M.op X2 X0)
       have j1 := eq450520 X0 x X2
       grind)
    | exact resolve eq226165 eq450520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226165 eq450520
  have eq455113 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq453340 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453340
  have eq455114 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq455113 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455113
  have eq455115 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq455114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455114
  have eq457836 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq455115 X1 (τ X0)
       grind)
    | exact superpose eq455115 eq19
    | (have j1 := eq455115 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq455115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq458209 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq455115 (σ X1) (σ X0)
       grind)
    | exact superpose eq455115 eq15
    | (have j1 := eq455115 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq455115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455115
  have eq462201 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq457836 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq457836
    | exact resolve eq457836 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457836
  have eq462797 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq462201 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq462201
    | (have j0 := eq462201 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq462201 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462201
  have eq470047 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq458209 x y
       grind)
    | exact superpose eq458209 eq16
    | (have j1 := eq458209 x y
       grind)
    | exact resolve eq16 eq458209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458209
  have eq472511 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq470047
       have i₂ := eq462797 x y
       grind)
    | exact superpose eq462797 eq470047
    | (have j1 := eq462797 (σ x) (σ y)
       grind)
    | (have r₁ := eq470047
       have r₂ := eq462797 x y
       grind)
    | (have r₁ := eq470047
       have r₂ := eq462797 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq470047
       have r₂ := eq462797 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq470047 eq462797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462797 eq470047
  have eq472514 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq472511
  have eq472518 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq472514
       grind)
    | exact superpose eq472514 eq16
    | exact resolve eq16 eq472514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472514
  have eq472519 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq472518
       have r₂ := eq22 x
       grind)
    | exact resolve eq472518 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472518
  have eq474757 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq472519
       grind)
    | exact superpose eq472519 eq16
    | exact resolve eq16 eq472519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474758 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq472519
       grind)
    | exact superpose eq472519 eq10
    | exact resolve eq10 eq472519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472519
  have eq475241 : x = y := by
    first
    | (have i₁ := eq474758
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq474758
    | exact resolve eq474758 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474758
  have eq475242 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq474757
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq474757
    | exact resolve eq474757 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq474757
  have eq475245 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq475242
       have i₂ := eq475241
       grind)
    | exact superpose eq475241 eq475242
    | exact resolve eq475242 eq475241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475241 eq475242
  have eq475246 : False := by grind
  exact eq475246

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_x_pxy_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  have eq51 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 X2))) ≠ X0 ∨ (M.op X1 (M.op X2 (M.op X0 X2))) = (M.op X1 X1) ∨ (M.op X1 (M.op X2 (M.op X0 X2))) = (k (M.op X1 (M.op X2 (M.op X0 X2))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op X2 (M.op X0 X2))) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X1 (M.op X2 (M.op X0 X2))) X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq110
    | exact resolve eq110 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq112
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq112
    | exact resolve eq112 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq500 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (M.op (σ y) X0))) = (M.op (M.op X1 (M.op (σ x) (σ y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ y) X1 (σ x) X0
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 X1) x X1 X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq525 : ∀ X0 X1 X2 : G, x = (M.op (M.op X0 (M.op X1 (M.op X2 X1))) (M.op (M.op y (M.op x y)) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op (M.op y sF0) (M.op X2 X0))
       have i₂ := eq53 X0 (M.op y sF0) X2 x
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op y (M.op x y))) (M.op (M.op X1 (M.op X2 X1)) (M.op X0 x))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq689 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq793 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X0) ≠ X2 ∨ (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X2)) X0) ∨ (M.op (M.op X0 (M.op X1 X2)) X0) = (k (M.op (M.op X0 (M.op X1 X2)) X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq75 X0 X2 x
       have i₂ := eq53 X0 X1 X2 x
       grind)
    | exact superpose eq53 eq75
    | (have r₁ := eq75 (M.op X2 (M.op x (M.op X0 x))) (M.op (M.op X2 (M.op (M.op X2 (M.op x (M.op X0 x))) X2)) (M.op X2 X0)) X2
       have r₂ := eq53 X0 (M.op X2 (M.op (M.op X2 (M.op x (M.op X0 x))) X2)) X2 x
       grind)
    | exact resolve eq75 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq75
  have eq817 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq506 X2 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq506
    | exact resolve eq506 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1299 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X1) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq506 X2 (M.op X1 X2) (M.op X0 X1)
       have i₂ := eq817 X1 X2 X0
       grind)
    | exact superpose eq817 eq506
    | exact resolve eq506 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq2856 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op (M.op X1 X0) X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq817 (M.op (M.op X1 X0) X1) (M.op X1 X0) X2
       have i₂ := eq1299 (M.op X1 X0) X1 X0
       grind)
    | exact superpose eq1299 eq817
    | exact resolve eq817 eq1299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817 eq1299
  have eq12616 : ∀ X0 : G, x = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (M.op (M.op y (M.op x y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq500 eq525
    | exact resolve eq525 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500 eq525
  have eq12963 : ∀ X0 : G, x = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (M.op (M.op y (M.op x y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq12616
    | (have j0 := eq12616 X0
       grind)
    | exact resolve eq12616 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12616
  have eq65136 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq113 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65144 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq65136
    | exact resolve eq65136 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65136
  have eq65155 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq65144
       have r₂ := eq28
       grind)
    | exact resolve eq65144 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65144
  have eq65157 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq65155
    | exact resolve eq65155 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65155
  have eq65164 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq65157
  have eq65280 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq65164
    | exact resolve eq65164 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65164
  have eq65296 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq65280 eq113
    | exact resolve eq113 eq65280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65280
  have eq65311 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq65296
  have eq65313 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq65311
       have r₂ := eq28
       grind)
    | exact resolve eq65311 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65311
  have eq65437 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq65313
  have eq65552 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq65437
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq65437
    | exact resolve eq65437 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65437
  have eq65561 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq65552
       grind)
    | exact superpose eq65552 eq45
    | exact resolve eq45 eq65552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65552
  have eq65589 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq65561
    | exact resolve eq65561 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65561
  have eq66049 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq65589 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq65589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66059 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq66049
    | exact resolve eq66049 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66049
  have eq66070 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq66059
       have r₂ := eq28
       grind)
    | exact resolve eq66059 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66059
  have eq66072 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq66070
    | exact resolve eq66070 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66070
  have eq66073 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq66072
  have eq66081 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq66073
  have eq66197 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq66081
    | exact resolve eq66081 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66081
  have eq66337 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66197 eq65589
    | exact resolve eq65589 eq66197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65589 eq66197
  have eq66346 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq66337
  have eq66350 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq66346
       have r₂ := eq28
       grind)
    | exact resolve eq66346 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66346
  have eq66352 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66350 eq28
    | exact resolve eq28 eq66350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66354 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66350 eq74
    | (have r₁ := eq74
       have r₂ := eq66350
       grind)
    | exact resolve eq74 eq66350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq66350
  have eq66424 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq66354
  have eq129892 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66424 eq113
    | exact resolve eq113 eq66424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129915 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq129892
  have eq129929 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq129915
       have r₂ := eq66352
       grind)
    | exact resolve eq129915 eq66352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129915
  have eq129968 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq129929
  have eq130113 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq129968
    | exact resolve eq129968 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129968
  have eq130304 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq130113 eq113
    | exact resolve eq113 eq130113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq130113
  have eq130323 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq130304
  have eq130327 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq130323
       have r₂ := eq28
       grind)
    | exact resolve eq130323 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130323
  have eq130336 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq130327
  have eq130475 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq130336
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq130336
    | exact resolve eq130336 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130336
  have eq130484 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq130475
       grind)
    | exact superpose eq130475 eq45
    | exact resolve eq45 eq130475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130475
  have eq130516 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq130484
    | exact resolve eq130484 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130484
  have eq130756 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq130516 eq66424
    | exact resolve eq66424 eq130516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66424
  have eq130767 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq130756
  have eq130775 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq130767
       have r₂ := eq66352
       grind)
    | exact resolve eq130767 eq66352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66352 eq130767
  have eq130802 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq130775
  have eq130947 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq130802
    | exact resolve eq130802 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130802
  have eq130978 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq130947 eq130516
    | exact resolve eq130516 eq130947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130516 eq130947
  have eq130987 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq130978
  have eq130995 : x = (M.op x y) := by
    first
    | (have r₁ := eq130987
       have r₂ := eq28
       grind)
    | exact resolve eq130987 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130987
  have eq130997 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq130995 eq21
    | exact resolve eq21 eq130995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq131225 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq130997
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq130997
    | exact resolve eq130997 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130997
  have eq131235 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq131225 eq27
    | exact resolve eq27 eq131225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131742 : ∀ X0 : G, x = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (M.op (M.op y x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq130995 eq12963
    | exact resolve eq12963 eq130995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12963
  have eq132160 : ∀ X0 : G, (M.op (M.op y x) (M.op X0 x)) = X0 := by
    intro X0
    first
    | exact superpose eq131742 eq2856
    | exact resolve eq2856 eq131742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2856
  have eq132177 : x ≠ x ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq131742 eq793
    | (have r₁ := eq793 (M.op (M.op y x) (M.op (σ x) (σ y))) y x
       have r₂ := eq131742 (M.op y x)
       grind)
    | exact resolve eq793 eq131742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793 eq131742
  have eq132317 : x = (k x y) ∨ x = (M.op y y) := by grind
  clear eq132177
  have eq146132 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq132317
       grind)
    | exact superpose eq132317 eq45
    | exact resolve eq45 eq132317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq146149 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq689 x y
       have i₂ := eq132317
       grind)
    | exact superpose eq132317 eq689
    | (have j0 := eq689 x y
       grind)
    | exact resolve eq689 eq132317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132317
  have eq146151 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq146149
  have eq146159 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq146151
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq146151
    | exact resolve eq146151 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146151
  have eq146174 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq131225 eq146132
    | exact resolve eq146132 eq131225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146132
  have eq146177 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq146159
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq146159
    | exact resolve eq146159 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146159
  have eq146191 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq146174
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq146174
    | exact resolve eq146174 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146174
  have eq146193 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq146177
    | exact resolve eq146177 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146177
  have eq146205 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq131225 eq146191
    | exact resolve eq146191 eq131225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146191
  have eq146207 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq131225 eq146193
    | exact resolve eq146193 eq131225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146193
  have eq146214 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq146207
       have r₂ := eq28
       grind)
    | exact resolve eq146207 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146207
  have eq146221 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq146214
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq146214
    | exact resolve eq146214 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146214
  have eq146228 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq146221
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq146221
    | exact resolve eq146221 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146221
  have eq146235 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq131225 eq146228
    | exact resolve eq146228 eq131225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146228
  have eq147202 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq146235
  have eq147361 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq131235 eq147202
    | exact resolve eq147202 eq131235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131235 eq147202
  have eq147409 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq147361 eq146205
    | exact resolve eq146205 eq147361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146205 eq147361
  have eq147418 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq147409
  have eq147420 : x = (M.op y y) := by
    first
    | (have r₁ := eq147418
       have r₂ := eq28
       grind)
    | exact resolve eq147418 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147418
  have eq148593 : (M.op x y) = (k x y) := by grind
  have eq148658 : ∀ X0 : G, y = (M.op (M.op X0 (M.op y (M.op x y))) (M.op (M.op y x) (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq562 X0 y y
       have i₂ := eq147420
       grind)
    | exact superpose eq147420 eq562
    | exact resolve eq562 eq147420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562 eq147420
  have eq148727 : ∀ X0 : G, y = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq148658 X0
       have i₂ := eq132160 X0
       grind)
    | exact superpose eq132160 eq148658
    | exact resolve eq148658 eq132160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132160 eq148658
  have eq148753 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq148593
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq148593
    | exact resolve eq148593 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq148593
  have eq148778 : x = y := by
    first
    | exact superpose eq51 eq148727
    | exact resolve eq148727 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq148727
  have eq148792 : x = (k x y) := by
    first
    | exact superpose eq130995 eq148753
    | exact resolve eq148753 eq130995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130995 eq148753
  have eq148825 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq148778
       grind)
    | exact superpose eq148778 eq25
    | exact resolve eq25 eq148778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq149138 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq148825
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq148825
    | exact resolve eq148825 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148825
  have eq149248 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq131225 eq149138
    | exact resolve eq149138 eq131225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149138
  have eq150612 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq149248 eq27
    | exact resolve eq27 eq149248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq149248
  have eq150981 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq131225 eq150612
    | exact resolve eq150612 eq131225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150612
  have eq151109 : x = (k x x) := by
    first
    | (have i₁ := eq148792
       have i₂ := eq148778
       grind)
    | exact superpose eq148778 eq148792
    | exact resolve eq148792 eq148778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148778 eq148792
  have eq151830 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq689 x x
       have i₂ := eq151109
       grind)
    | exact superpose eq151109 eq689
    | (have j0 := eq689 x x
       grind)
    | exact resolve eq689 eq151109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689 eq151109
  have eq151833 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq151830
  have eq151834 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq151833
  have eq151845 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq151834
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq151834
    | exact resolve eq151834 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq151834
  have eq151863 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq131225 eq151845
    | exact resolve eq151845 eq131225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131225 eq151845
  have eq152893 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq151863 eq150981
    | exact resolve eq150981 eq151863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150981 eq151863
  have eq152894 : False := by grind
  exact eq152894

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_x_pxy_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq18
  have eq31 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq9 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
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
  clear eq22
  have eq185 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq313 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq301 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq318 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq317 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq320 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq313 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq313 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq313 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq313 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq329 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq318 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq318 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq318 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq544 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq329 (σ x) (σ y)
       grind)
    | exact superpose eq329 eq16
    | (have j1 := eq329 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq551 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq185 X0
       have i₂ := eq329 X0 X0
       grind)
    | exact superpose eq329 eq185
    | (have j0 := eq185 X0
       have j1 := eq329 X0 X0
       grind)
    | exact resolve eq185 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq555 : ∀ X0 : G, (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq551 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq561 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq544
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq544
    | exact resolve eq544 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq563 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq561
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq561
    | exact resolve eq561 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq632 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq563
       have i₂ := eq329 x y
       grind)
    | exact superpose eq329 eq563
    | (have j1 := eq329 x y
       grind)
    | exact resolve eq563 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq633 : (σ x) = (σ (k x y)) ∨ x = (k x y) := by grind
  clear eq632
  have eq634 : (k x y) = (τ (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq633
       grind)
    | exact superpose eq633 eq10
    | exact resolve eq10 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq675 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq634
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq634
    | exact resolve eq634 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq676 : x = (k x y) := by grind
  clear eq675
  have eq681 : ∀ X0 X1 : G, (τ (k X0 X1)) ≠ (M.op (τ X0) (τ X0)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq320 (τ X1) (τ X0)
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq320
    | exact resolve eq320 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq813 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 x
       have i₂ := eq31 X2 X0 X1 x
       grind)
    | exact superpose eq31 eq9
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq827 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X0) X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 x X0
       have i₂ := eq31 (M.op X2 X0) x X0 X1
       grind)
    | exact superpose eq31 eq9
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2009 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X0 X0)) X1) X0) = X2 ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq813 X1 X0 X2
       have i₂ := eq14 X0 X2
       grind)
    | (have i₁ := eq813 X0 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq813
    | (have j1 := eq14 X0 X2
       grind)
    | exact resolve eq813 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2048 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X0 X0)) X1) X0) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2009 X0 X1 X2
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq2009 X0 X1 (M.op (M.op (M.op (M.op X1 (M.op X0 X0)) X1) X0) (M.op (M.op (M.op X1 (M.op X0 X0)) X1) X0))
       have r₂ := eq12 X0 (M.op (M.op (M.op X1 (M.op X0 X0)) X1) X0)
       grind)
    | (have r₁ := eq2009 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq2009 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2009
  have eq2050 : ∀ X0 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ X0 = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq2048 X0 x X2
       have i₂ := eq813 x X0 X0
       grind)
    | exact superpose eq813 eq2048
    | (have j0 := eq2048 X0 x X2
       grind)
    | exact resolve eq2048 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048
  have eq2087 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2050 (σ x) (σ y)
       grind)
    | exact superpose eq2050 eq16
    | (have j1 := eq2050 (σ x) (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq2050 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq2050 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq2050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2090 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2087
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq2087
    | exact resolve eq2087 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2087
  have eq2092 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2090
       have i₂ := eq676
       grind)
    | exact superpose eq676 eq2090
    | exact resolve eq2090 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090
  have eq2094 : (σ x) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2092
       have i₂ := eq2050 x y
       grind)
    | exact superpose eq2050 eq2092
    | (have j1 := eq2050 (σ x) (σ y)
       grind)
    | (have r₁ := eq2092
       have r₂ := eq2050 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq2092
       have r₂ := eq2050 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq2092 eq2050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2050 eq2092
  have eq2096 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2094
       have i₂ := eq676
       grind)
    | exact superpose eq676 eq2094
    | exact resolve eq2094 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676 eq2094
  have eq2097 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2096
  have eq2125 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2097
       grind)
    | exact superpose eq2097 eq10
    | exact resolve eq10 eq2097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2097
  have eq2190 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2125
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2125
    | exact resolve eq2125 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2125
  have eq2191 : x = y := by grind
  clear eq2190
  have eq2192 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2191
       grind)
    | exact superpose eq2191 eq16
    | exact resolve eq16 eq2191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2191
  have eq2201 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq2192
       have i₂ := eq14 (σ x) X0
       grind)
    | (have i₁ := eq2192
       have i₂ := eq14 (σ x) (σ x)
       grind)
    | exact superpose eq14 eq2192
    | (have j1 := eq14 (σ x) X0
       grind)
    | exact resolve eq2192 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2205 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) X0) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq2201 X0
       have j1 := eq12 (σ x) X0
       grind)
    | (have r₁ := eq2201 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq2201 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2201
  have eq2867 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ X0 ∨ (k (σ x) (M.op X1 (M.op (M.op X0 (σ x)) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2205 (M.op X1 (M.op (M.op x (σ x)) X1))
       have i₂ := eq827 (σ x) X1 x
       grind)
    | exact superpose eq827 eq2205
    | (have r₁ := eq2205 (M.op X1 (M.op (M.op (σ (M.op x x)) (σ x)) X1))
       have r₂ := eq827 (σ x) X1 (σ (M.op x x))
       grind)
    | exact resolve eq2205 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2205
  have eq2880 : ∀ X0 : G, (σ (M.op x x)) = (k (σ x) (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0))) := by
    intro X0
    first
    | (have j0 := eq2867 (σ (M.op x x)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2867
  have eq2919 : ∀ X0 : G, (k x (τ (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0)))) = (τ (σ (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq28 x (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0))
       have i₂ := eq2880 X0
       grind)
    | exact superpose eq2880 eq28
    | exact resolve eq28 eq2880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq2927 : ∀ X0 : G, (τ (σ (M.op x x))) ≠ (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ (M.op x x))) = (M.op (τ (σ x)) (τ (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0)))) := by
    intro X0
    first
    | (have i₁ := eq681 (σ x) (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0))
       have i₂ := eq2880 X0
       grind)
    | exact superpose eq2880 eq681
    | exact resolve eq681 eq2880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681 eq2880
  have eq2929 : ∀ X0 : G, (M.op x x) ≠ (τ (σ (M.op x x))) ∨ (τ (σ (M.op x x))) = (M.op (τ (σ x)) (τ (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0)))) := by
    intro X0
    first
    | (have i₁ := eq2927 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2927
    | (have j0 := eq2927 X0
       grind)
    | exact resolve eq2927 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2927
  have eq2936 : ∀ X0 : G, (M.op x x) = (k x (τ (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0)))) := by
    intro X0
    first
    | (have i₁ := eq2919 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq2919
    | exact resolve eq2919 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2919
  have eq2942 : ∀ X0 : G, (τ (σ (M.op x x))) = (M.op (τ (σ x)) (τ (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0)))) := by
    intro X0
    first
    | (have j0 := eq2929 X0
       grind)
    | (have r₁ := eq2929 X0
       have r₂ := eq10 (M.op x x)
       grind)
    | exact resolve eq2929 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2929
  have eq2948 : ∀ X0 : G, (τ (σ (M.op x x))) = (M.op x (τ (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0)))) := by
    intro X0
    first
    | (have i₁ := eq2942 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2942
    | exact resolve eq2942 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2942
  have eq2949 : ∀ X0 : G, (M.op x x) = (M.op x (τ (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0)))) := by
    intro X0
    first
    | (have i₁ := eq2948 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq2948
    | exact resolve eq2948 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2948
  have eq3446 : ∀ X0 : G, (M.op x x) ≠ (M.op x x) ∨ (τ (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0))) = (M.op (τ (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0))) (τ (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0)))) ∨ x = (k x (τ (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0)))) := by
    intro X0
    first
    | (have i₁ := eq13 x (τ (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0)))
       have i₂ := eq2949 X0
       grind)
    | exact superpose eq2949 eq13
    | (have j0 := eq13 x (τ (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0)))
       grind)
    | (have r₁ := eq13 x (τ (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0)))
       have r₂ := eq2949 X0
       grind)
    | exact resolve eq13 eq2949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3460 : ∀ X0 X1 : G, (τ (M.op X1 (M.op (M.op (σ (M.op x x)) (σ x)) X1))) = (M.op (M.op (M.op X0 (M.op x x)) X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq813 X0 x (τ (M.op X1 (M.op (M.op (σ (M.op x x)) (σ x)) X1)))
       have i₂ := eq2949 X1
       grind)
    | exact superpose eq2949 eq813
    | exact resolve eq813 eq2949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2949
  have eq3463 : ∀ X0 : G, (τ (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0))) = (M.op (τ (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0))) (τ (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0)))) ∨ x = (k x (τ (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0)))) := by
    intro X0
    first
    | (have j0 := eq3446 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3446
  have eq3464 : ∀ X1 : G, x = (τ (M.op X1 (M.op (M.op (σ (M.op x x)) (σ x)) X1))) := by
    intro X1
    first
    | (have i₁ := eq3460 x X1
       have i₂ := eq813 x x x
       grind)
    | exact superpose eq813 eq3460
    | exact resolve eq3460 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3460
  have eq3465 : ∀ X0 : G, x = (M.op x x) ∨ (τ (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0))) = (M.op (τ (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0))) (τ (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0)))) := by
    intro X0
    first
    | (have i₁ := eq3463 X0
       have i₂ := eq2936 X0
       grind)
    | exact superpose eq2936 eq3463
    | (have j0 := eq3463 X0
       grind)
    | exact resolve eq3463 eq2936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3463
  have eq3477 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3465 x
       have i₂ := eq3464 x
       grind)
    | exact superpose eq3464 eq3465
    | exact resolve eq3465 eq3464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3464 eq3465
  have eq3478 : x = (M.op x x) := by grind
  clear eq3477
  have eq3495 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op x X0))) = (M.op (M.op X1 x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 x X1 x X0
       have i₂ := eq3478
       grind)
    | exact superpose eq3478 eq31
    | exact resolve eq31 eq3478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3497 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 (M.op X1 X0)) (M.op x x))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 x X0 X1 x
       have i₂ := eq3478
       grind)
    | exact superpose eq3478 eq32
    | exact resolve eq32 eq3478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3508 : ∀ X0 : G, x = (M.op x (M.op X0 (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq827 x X0 x
       have i₂ := eq3478
       grind)
    | exact superpose eq3478 eq827
    | exact resolve eq827 eq3478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq3509 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq3478
       grind)
    | exact superpose eq3478 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq3478
       grind)
    | exact resolve eq12 eq3478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3514 : ∀ X0 : G, x ≠ (k x X0) ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq320 x X0
       have i₂ := eq3478
       grind)
    | exact superpose eq3478 eq320
    | (have j0 := eq320 x X0
       grind)
    | exact resolve eq320 eq3478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320 eq3478
  have eq3517 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq3509 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3509
  have eq3521 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq3514 X0
       have j1 := eq329 x X0
       grind)
    | (have r₁ := eq3514 x
       have r₂ := eq329 x x
       grind)
    | exact resolve eq3514 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329 eq3514
  have eq3524 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 (M.op X1 X0)) (k x x))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3497 X0 X1
       have i₂ := eq3517 x
       grind)
    | exact superpose eq3517 eq3497
    | exact resolve eq3497 eq3517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3497
  have eq3526 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op x X0))) = (M.op (k X1 x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3495 X0 X1
       have i₂ := eq3517 X1
       grind)
    | exact superpose eq3517 eq3495
    | exact resolve eq3495 eq3517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3495
  have eq3532 : ∀ X0 X1 : G, (k x (M.op (M.op X0 (M.op X1 X0)) (k x x))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3524 X0 X1
       have i₂ := eq3521 (M.op (M.op X0 (M.op X1 X0)) (k x x))
       grind)
    | exact superpose eq3521 eq3524
    | exact resolve eq3524 eq3521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3524
  have eq3534 : ∀ X1 : G, x = (M.op (k X1 x) X1) := by
    intro X1
    first
    | (have i₁ := eq3526 x X1
       have i₂ := eq3508 x
       grind)
    | exact superpose eq3508 eq3526
    | exact resolve eq3526 eq3508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3508 eq3526
  have eq3536 : ∀ X0 X1 : G, (k x (M.op (M.op X0 (M.op X1 X0)) x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3532 X0 X1
       have i₂ := eq555 x
       grind)
    | exact superpose eq555 eq3532
    | exact resolve eq3532 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3532
  have eq3539 : ∀ X0 X1 : G, (k x (k (M.op X0 (M.op X1 X0)) x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3536 X0 X1
       have i₂ := eq3517 (M.op X0 (M.op X1 X0))
       grind)
    | exact superpose eq3517 eq3536
    | exact resolve eq3536 eq3517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3536
  have eq3579 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X1 X2))) = (k (M.op x (M.op X0 X1)) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X1 x X0 X2
       have i₂ := eq3517 (M.op x (M.op X0 X1))
       grind)
    | exact superpose eq3517 eq31
    | exact resolve eq31 eq3517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq3599 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X1 X2))) = (k (k x (M.op X0 X1)) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3579 X0 X1 X2
       have i₂ := eq3521 (M.op X0 X1)
       grind)
    | exact superpose eq3521 eq3579
    | exact resolve eq3579 eq3521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3579
  have eq3907 : ∀ X0 X1 X2 : G, (k x (M.op (M.op X0 (M.op X1 X0)) (M.op X2 (M.op x X2)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 x X0 X1 X2
       have i₂ := eq3521 (M.op (M.op X0 (M.op X1 X0)) (M.op X2 (M.op x X2)))
       grind)
    | exact superpose eq3521 eq32
    | exact resolve eq32 eq3521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq3920 : ∀ X0 X1 : G, (k x (k (k x (M.op (M.op X0 (M.op X1 X0)) x)) x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3907 X0 X1 x
       have i₂ := eq3599 (M.op X0 (M.op X1 X0)) x x
       grind)
    | exact superpose eq3599 eq3907
    | exact resolve eq3907 eq3599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3599 eq3907
  have eq3961 : ∀ X0 X1 : G, (k x (k (k x (k (M.op X0 (M.op X1 X0)) x)) x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3920 X0 X1
       have i₂ := eq3517 (M.op X0 (M.op X1 X0))
       grind)
    | exact superpose eq3517 eq3920
    | exact resolve eq3920 eq3517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3920
  have eq3972 : ∀ X1 : G, (k x (k X1 x)) = X1 := by
    intro X1
    first
    | (have i₁ := eq3961 x X1
       have i₂ := eq3539 x X1
       grind)
    | exact superpose eq3539 eq3961
    | exact resolve eq3961 eq3539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3539 eq3961
  have eq4006 : ∀ X0 X1 : G, (M.op (M.op x (k (M.op X0 X1) x)) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq813 (k (M.op X0 X1) x) X0 X1
       have i₂ := eq3534 (M.op X0 X1)
       grind)
    | exact superpose eq3534 eq813
    | exact resolve eq813 eq3534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813 eq3534
  have eq4018 : ∀ X0 X1 : G, (M.op (k x (k (M.op X0 X1) x)) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4006 X0 X1
       have i₂ := eq3521 (k (M.op X0 X1) x)
       grind)
    | exact superpose eq3521 eq4006
    | exact resolve eq4006 eq3521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4006
  have eq4037 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4018 X0 X1
       have i₂ := eq3972 (M.op X0 X1)
       grind)
    | (have i₁ := eq4018 X0 X1
       have i₂ := eq3972 (k x (k (M.op X0 X1) x))
       grind)
    | exact superpose eq3972 eq4018
    | exact resolve eq4018 eq3972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3972 eq4018
  have eq4116 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 x X0
       have i₂ := eq4037 x (M.op X0 (M.op X1 X0))
       grind)
    | exact superpose eq4037 eq9
    | exact resolve eq9 eq4037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4150 : ∀ X0 : G, (k (M.op x X0) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq3517 (M.op x X0)
       have i₂ := eq4037 x X0
       grind)
    | exact superpose eq4037 eq3517
    | exact resolve eq3517 eq4037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4037
  have eq4151 : ∀ X0 : G, (k (k x X0) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq4150 X0
       have i₂ := eq3521 X0
       grind)
    | exact superpose eq3521 eq4150
    | exact resolve eq4150 eq3521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3521 eq4150
  have eq4681 : ∀ X0 : G, (τ (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0))) = (k (M.op x x) x) := by
    intro X0
    first
    | (have i₁ := eq4151 (τ (M.op X0 (M.op (M.op (σ (M.op x x)) (σ x)) X0)))
       have i₂ := eq2936 X0
       grind)
    | exact superpose eq2936 eq4151
    | exact resolve eq4151 eq2936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2936
  have eq4689 : ∀ X0 : G, (τ (M.op X0 (M.op (M.op (σ (k x x)) (σ x)) X0))) = (k (k x x) x) := by
    intro X0
    first
    | (have i₁ := eq4681 X0
       have i₂ := eq3517 x
       grind)
    | exact superpose eq3517 eq4681
    | exact resolve eq4681 eq3517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4681
  have eq4691 : ∀ X0 : G, x = (τ (M.op X0 (M.op (M.op (σ (k x x)) (σ x)) X0))) := by
    intro X0
    first
    | (have i₁ := eq4689 X0
       have i₂ := eq4151 x
       grind)
    | exact superpose eq4151 eq4689
    | exact resolve eq4689 eq4151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4151 eq4689
  have eq4692 : x = (τ (M.op (σ (k x x)) (σ x))) := by
    first
    | (have i₁ := eq4691 x
       have i₂ := eq4116 x (M.op (σ (k x x)) (σ x))
       grind)
    | exact superpose eq4116 eq4691
    | exact resolve eq4691 eq4116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4116 eq4691
  have eq4693 : x = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq4692
       have i₂ := eq555 x
       grind)
    | exact superpose eq555 eq4692
    | exact resolve eq4692 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4692
  have eq4801 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ x))
       have i₂ := eq4693
       grind)
    | exact superpose eq4693 eq11
    | exact resolve eq11 eq4693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4693
  have eq5309 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2192
       have i₂ := eq4801
       grind)
    | exact superpose eq4801 eq2192
    | exact resolve eq2192 eq4801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2192 eq4801
  have eq5358 : (σ x) ≠ (σ (k x x)) := by
    first
    | (have i₁ := eq5309
       have i₂ := eq3517 x
       grind)
    | exact superpose eq3517 eq5309
    | exact resolve eq5309 eq3517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3517 eq5309
  have eq5370 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq5358
       have i₂ := eq555 x
       grind)
    | exact superpose eq555 eq5358
    | exact resolve eq5358 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555 eq5358
  have eq5371 : False := by grind
  exact eq5371

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pyx_pyy_pyx_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq39 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq9 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) (M.op X3 (M.op X1 X3))) = (M.op (M.op X4 X0) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq39 X1 X4 (M.op X1 (M.op X2 (M.op X0 X2))) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq39
    | exact resolve eq39 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 x
       have i₂ := eq39 X2 X0 X1 x
       grind)
    | exact superpose eq39 eq9
    | exact resolve eq9 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq124 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq124 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq124 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq125 (σ X0)
       grind)
    | exact superpose eq125 eq15
    | exact resolve eq15 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq128 X0
       have i₂ := eq125 X0
       grind)
    | exact superpose eq125 eq128
    | exact resolve eq128 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq128
  have eq150 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (M.op X1 (σ (M.op X0 X0))) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X1 (σ X0) (σ X0)
       have i₂ := eq139 X0
       grind)
    | exact superpose eq139 eq79
    | exact resolve eq79 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  have eq162 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq159 (σ X1) (σ X0)
       grind)
    | exact superpose eq159 eq15
    | (have j1 := eq159 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq162 X0 X1
       have i₂ := eq139 X1
       grind)
    | exact superpose eq139 eq162
    | (have j0 := eq162 X0 X1
       grind)
    | exact resolve eq162 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq652 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X4) = (M.op (M.op X1 (M.op X0 X1)) (M.op X2 (M.op (M.op X3 (M.op X4 X3)) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq39 (M.op X3 (M.op X4 X3)) X4 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq40 X4 X1 X0 X3
       grind)
    | exact superpose eq40 eq39
    | exact resolve eq39 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq40
  have eq691 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq169 x y
       grind)
    | exact superpose eq169 eq16
    | (have j1 := eq169 x y
       grind)
    | exact resolve eq16 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq17154 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op (M.op X6 (M.op X4 (M.op X1 X4))) X6) = (M.op (M.op X0 X1) (M.op X5 (M.op (M.op X2 (M.op X0 X2)) X5))) := by
    intro X0 X1 X2 X4 X5 X6
    first
    | (have i₁ := eq70 (M.op X4 (M.op X1 X4)) (M.op X2 (M.op X0 X2)) x X5 X6
       have i₂ := eq652 X0 X2 x X4 X1
       grind)
    | exact superpose eq652 eq70
    | exact resolve eq70 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq652
  have eq17366 : ∀ X0 X1 X2 X5 : G, (M.op (M.op X0 X1) (M.op X5 (M.op (M.op X2 (M.op X0 X2)) X5))) = X1 := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq17154 X0 X1 X2 x X5 x
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq17154
    | exact resolve eq17154 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17154
  have eq20361 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq691
       have i₂ := eq159 y x
       grind)
    | exact superpose eq159 eq691
    | (have j1 := eq159 y x
       grind)
    | exact resolve eq691 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq691
  have eq20362 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq20361
  have eq62620 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (σ (M.op y y))) X0) (σ y)) ∨ (M.op y y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq79 X0 (σ y) (σ x)
       have i₂ := eq20362
       grind)
    | exact superpose eq20362 eq79
    | exact resolve eq79 eq20362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq20362
  have eq62740 : (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq62620 x
       have i₂ := eq150 y x
       grind)
    | exact superpose eq150 eq62620
    | exact resolve eq62620 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq62620
  have eq62902 : ∀ X0 X1 : G, y = (M.op (M.op y x) (M.op X0 (M.op (M.op X1 (M.op y X1)) X0))) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq17366 y y X1 X0
       have i₂ := eq62740
       grind)
    | exact superpose eq62740 eq17366
    | exact resolve eq17366 eq62740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62740
  have eq62905 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq62902 x x
       have i₂ := eq17366 y x x x
       grind)
    | exact superpose eq17366 eq62902
    | exact resolve eq62902 eq17366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17366 eq62902
  have eq62929 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq62905
       grind)
    | exact superpose eq62905 eq10
    | exact resolve eq10 eq62905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62905
  have eq62981 : x = y ∨ x = y := by
    first
    | (have i₁ := eq62929
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq62929
    | exact resolve eq62929 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62929
  have eq62982 : x = y := by grind
  clear eq62981
  have eq62986 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq62982
       grind)
    | exact superpose eq62982 eq16
    | exact resolve eq16 eq62982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62982
  have eq62987 : False := by grind
  exact eq62987

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pxy_pyy_pxy_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq9 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq42 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq42 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq56 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
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
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq56
    | (have j0 := eq56 (σ X0) (σ X1)
       grind)
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq43 (τ X0)
       grind)
    | exact superpose eq43 eq18
    | exact resolve eq18 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq83 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq83
    | exact resolve eq83 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq83
  have eq95 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq91
    | exact resolve eq91 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq109 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 (M.op X1 X2)) X0) = (M.op (M.op X4 (M.op X1 X2)) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq23 X2 X4 X1 x
       have i₂ := eq23 X2 X0 X1 x
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (M.op X0 X1) x X1 X2
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) (M.op X4 (M.op X3 X4)))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X3 (M.op X1 X2) X2 X4
       have i₂ := eq23 X1 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq23 eq24
    | exact resolve eq24 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X0 X2)) (M.op (M.op X4 (M.op X5 X4)) (M.op X3 (M.op X0 (M.op X1 (M.op X2 X1)))))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 (M.op X3 (M.op X0 X2)) X4 X5 X3
       have i₂ := eq23 X2 X3 X0 X1
       grind)
    | exact superpose eq23 eq24
    | exact resolve eq24 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq167 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67 x y
       grind)
    | exact superpose eq67 eq16
    | (have j1 := eq67 x y
       grind)
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq187 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq9
    | exact resolve eq9 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op X1 (M.op (σ (M.op X0 X0)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq187 X0 x
       have i₂ := eq23 (σ (M.op X0 X0)) x (σ X0) X1
       grind)
    | exact superpose eq23 eq187
    | exact resolve eq187 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq518 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq167
       have i₂ := eq95 x
       grind)
    | exact superpose eq95 eq167
    | exact resolve eq167 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq545 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq518
       have i₂ := eq56 x y
       grind)
    | exact superpose eq56 eq518
    | (have j1 := eq56 x y
       grind)
    | exact resolve eq518 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq518
  have eq546 : (M.op x x) = (M.op y x) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by grind
  clear eq545
  have eq561 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ (M.op X0 X0))) (M.op X1 (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq116 X1 (M.op (σ X0) (σ (M.op X0 X0))) X1
       have i₂ := eq187 X0 X1
       grind)
    | exact superpose eq187 eq116
    | exact resolve eq116 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq991 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X0) X3) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq109 X0 (M.op (σ X0) (σ (M.op X0 X0))) (M.op X1 (σ X0)) x
       have i₂ := eq561 X0 X1
       grind)
    | exact superpose eq561 eq109
    | exact resolve eq109 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq561
  have eq1475 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq116 X2 X1 X2
       have i₂ := eq991 X1 X0 X2
       grind)
    | (have i₁ := eq116 X2 X1 X2
       have i₂ := eq991 X1 X2 X0
       grind)
    | exact superpose eq991 eq116
    | exact resolve eq116 eq991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq2377 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (M.op X0 X1) X0) X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1475 (M.op (M.op X0 X1) X0) X2 X1
       have i₂ := eq1475 X0 X1 (M.op (M.op (M.op X0 X1) X0) X2)
       grind)
    | exact superpose eq1475 eq1475
    | exact resolve eq1475 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475
  have eq13588 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op (M.op X2 (M.op (M.op X3 X0) X3)) X2) X1)) (M.op (M.op X4 (M.op X5 X4)) X0)) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq136 (M.op (M.op X2 (M.op (M.op X3 X0) X3)) X2) x X1 X1 X4 X5
       have i₂ := eq134 X2 X3 X0 X1 x
       grind)
    | exact superpose eq134 eq136
    | exact resolve eq136 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq136
  have eq13924 : ∀ X0 X3 X4 X5 : G, (M.op (M.op (M.op X3 X0) X3) (M.op (M.op X4 (M.op X5 X4)) X0)) = X5 := by
    intro X0 X3 X4 X5
    first
    | (have i₁ := eq13588 X0 x x X3 X4 X5
       have i₂ := eq2377 x (M.op (M.op X3 X0) X3) x
       grind)
    | exact superpose eq2377 eq13588
    | exact resolve eq13588 eq2377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2377 eq13588
  have eq43054 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op x (M.op x x)) X1)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq13924 X1 X0 x y
       have i₂ := eq546
       grind)
    | exact superpose eq546 eq13924
    | exact resolve eq13924 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq43057 : x = y ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43054 x x
       have i₂ := eq13924 x x x x
       grind)
    | (have i₁ := eq43054 x x
       have i₂ := eq13924 x x x (M.op (M.op (M.op x x) x) (M.op (M.op x (M.op x x)) x))
       grind)
    | exact superpose eq13924 eq43054
    | exact resolve eq43054 eq13924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13924 eq43054
  have eq43093 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq43057
       grind)
    | exact superpose eq43057 eq16
    | exact resolve eq16 eq43057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43057
  have eq43094 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq43093
       have r₂ := eq95 x
       grind)
    | exact resolve eq43093 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43093
  have eq43264 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op X0 (M.op (σ (M.op x x)) X0))) := by
    intro X0
    first
    | (have i₁ := eq116 (σ y) (σ x) X0
       have i₂ := eq43094
       grind)
    | exact superpose eq43094 eq116
    | exact resolve eq116 eq43094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq43094
  have eq43358 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq43264 x
       have i₂ := eq387 x x
       grind)
    | exact superpose eq387 eq43264
    | exact resolve eq43264 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387 eq43264
  have eq43425 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq43358
       grind)
    | exact superpose eq43358 eq10
    | exact resolve eq10 eq43358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43358
  have eq43481 : x = y := by
    first
    | (have i₁ := eq43425
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq43425
    | exact resolve eq43425 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43425
  have eq45190 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq43481
       grind)
    | exact superpose eq43481 eq16
    | exact resolve eq16 eq43481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43481
  have eq45193 : False := by grind
  exact eq45193

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_x_pxy_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq31 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq9 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq307 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X0 X0))) X1) = X2 ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq9 X1 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq310 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq316 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq311 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq311 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq311 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq311 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq317 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq310 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq310 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq310 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq319 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X0 X0))) X1) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq307 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq307 X0 X1 (M.op (M.op (M.op X1 (M.op X0 (M.op X0 X0))) X1) (M.op (M.op X1 (M.op X0 (M.op X0 X0))) X1))
       have r₂ := eq12 X0 (M.op (M.op X1 (M.op X0 (M.op X0 X0))) X1)
       grind)
    | (have r₁ := eq307 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq307 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq327 : ∀ X0 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ X0 = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq319 X0 x X2
       have i₂ := eq9 X0 x X0
       grind)
    | exact superpose eq9 eq319
    | (have j0 := eq319 X0 x X2
       grind)
    | exact resolve eq319 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq333 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq327 (σ y) (σ x)
       grind)
    | exact superpose eq327 eq16
    | (have j1 := eq327 (σ x) (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq327 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq327 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq333
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq333
    | exact resolve eq333 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq342 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq339
       have i₂ := eq327 y x
       grind)
    | exact superpose eq327 eq339
    | (have j1 := eq327 (σ x) (σ y)
       grind)
    | (have r₁ := eq339
       have r₂ := eq327 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq339
       have r₂ := eq327 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq339 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327 eq339
  have eq343 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq342
  have eq345 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq343
       grind)
    | exact superpose eq343 eq10
    | exact resolve eq10 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq362 : x = y ∨ x = y := by
    first
    | (have i₁ := eq345
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq345
    | exact resolve eq345 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq363 : x = y := by grind
  clear eq362
  have eq364 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq363
       grind)
    | exact superpose eq363 eq16
    | exact resolve eq16 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq367 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq317 X0 X0
       have i₂ := eq186 X0
       grind)
    | exact superpose eq186 eq317
    | (have j1 := eq186 X0
       grind)
    | (have r₁ := eq317 X0 X0
       have r₂ := eq186 X0
       grind)
    | exact resolve eq317 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq317
  have eq369 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq367 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq370 : ∀ X0 : G, (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq369 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq423 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op X0 (σ x)) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq364
       have i₂ := eq14 X0 (σ x)
       grind)
    | (have i₁ := eq364
       have i₂ := eq14 (σ x) (σ x)
       grind)
    | exact superpose eq14 eq364
    | (have j1 := eq14 X0 (σ x)
       grind)
    | exact resolve eq364 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op X0 (σ x)) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq423 X0
       have j1 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq423 X0
       have r₂ := eq12 X0 (σ x)
       grind)
    | exact resolve eq423 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq598 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ X0 ∨ (k (M.op (σ x) (M.op X1 (M.op X0 X1))) (σ x)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq425 (M.op (σ x) (M.op x (M.op X0 x)))
       have i₂ := eq9 X0 (σ x) x
       grind)
    | exact superpose eq9 eq425
    | (have r₁ := eq425 (M.op (σ x) (M.op x (M.op (σ (M.op x x)) x)))
       have r₂ := eq9 (σ (M.op x x)) (σ x) x
       grind)
    | exact resolve eq425 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq687 : ∀ X0 : G, (σ (M.op x x)) = (k (M.op (σ x) (M.op X0 (M.op (σ (M.op x x)) X0))) (σ x)) := by
    intro X0
    first
    | (have j0 := eq598 (σ (M.op x x)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq707 : ∀ X0 : G, (k (τ (M.op (σ x) (M.op X0 (M.op (σ (M.op x x)) X0)))) x) = (τ (σ (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq22 (M.op (σ x) (M.op X0 (M.op (σ (M.op x x)) X0))) x
       have i₂ := eq687 X0
       grind)
    | exact superpose eq687 eq22
    | exact resolve eq22 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq687
  have eq709 : ∀ X0 : G, (M.op x x) = (k (τ (M.op (σ x) (M.op X0 (M.op (σ (M.op x x)) X0)))) x) := by
    intro X0
    first
    | (have i₁ := eq707 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq707
    | exact resolve eq707 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq728 : ∀ X0 : G, (M.op x x) = (k (τ (M.op (M.op X0 (M.op (σ x) (σ (M.op x x)))) X0)) x) := by
    intro X0
    first
    | (have i₁ := eq709 x
       have i₂ := eq31 (σ (M.op x x)) X0 (σ x) x
       grind)
    | exact superpose eq31 eq709
    | exact resolve eq709 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq734 : ∀ X0 : G, (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op (τ (M.op (σ x) (M.op X0 (M.op (σ (M.op x x)) X0)))) x) := by
    intro X0
    first
    | (have i₁ := eq316 (τ (M.op (σ x) (M.op X0 (M.op (σ (M.op x x)) X0)))) x
       have i₂ := eq709 X0
       grind)
    | exact superpose eq709 eq316
    | (have r₁ := eq316 (τ (M.op (σ x) (M.op X0 (M.op (σ (M.op x x)) X0)))) x
       have r₂ := eq709 X0
       grind)
    | exact resolve eq316 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq735 : ∀ X0 : G, (M.op x x) = (M.op (τ (M.op (σ x) (M.op X0 (M.op (σ (M.op x x)) X0)))) x) := by
    intro X0
    first
    | (have j0 := eq734 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq852 : ∀ X0 : G, (M.op x x) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (τ (M.op (σ x) (M.op X0 (M.op (σ (M.op x x)) X0)))) = (k (τ (M.op (σ x) (M.op X0 (M.op (σ (M.op x x)) X0)))) x) := by
    intro X0
    first
    | (have i₁ := eq13 (τ (M.op (σ x) (M.op X0 (M.op (σ (M.op x x)) X0)))) x
       have i₂ := eq735 X0
       grind)
    | exact superpose eq735 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 (τ (M.op (σ x) (M.op X0 (M.op (σ (M.op x x)) X0)))) x
       have r₂ := eq735 X0
       grind)
    | exact resolve eq13 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq854 : ∀ X0 X1 X2 : G, (τ (M.op (σ x) (M.op X1 (M.op (σ (M.op x x)) X1)))) = (M.op X0 (M.op (M.op x (M.op x x)) (M.op X2 (M.op X0 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X0 x (τ (M.op (σ x) (M.op X1 (M.op (σ (M.op x x)) X1)))) X2
       have i₂ := eq735 X1
       grind)
    | exact superpose eq735 eq32
    | exact resolve eq32 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq859 : ∀ X0 : G, x = (M.op x x) ∨ (τ (M.op (σ x) (M.op X0 (M.op (σ (M.op x x)) X0)))) = (k (τ (M.op (σ x) (M.op X0 (M.op (σ (M.op x x)) X0)))) x) := by
    intro X0
    first
    | (have j0 := eq852 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq860 : ∀ X1 : G, x = (τ (M.op (σ x) (M.op X1 (M.op (σ (M.op x x)) X1)))) := by
    intro X1
    first
    | (have i₁ := eq854 x X1 x
       have i₂ := eq32 x x x x
       grind)
    | exact superpose eq32 eq854
    | exact resolve eq854 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq861 : ∀ X0 : G, (M.op x x) = (τ (M.op (σ x) (M.op X0 (M.op (σ (M.op x x)) X0)))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq859 X0
       have i₂ := eq709 X0
       grind)
    | exact superpose eq709 eq859
    | exact resolve eq859 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709 eq859
  have eq869 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq861 x
       have i₂ := eq860 x
       grind)
    | exact superpose eq860 eq861
    | exact resolve eq861 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860 eq861
  have eq870 : x = (M.op x x) := by grind
  clear eq869
  have eq880 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq870
       grind)
    | exact superpose eq870 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq870
       grind)
    | exact resolve eq12 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq881 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 x
       have i₂ := eq870
       grind)
    | exact superpose eq870 eq9
    | exact resolve eq9 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq883 : ∀ X0 X1 : G, x = (M.op X0 (M.op (M.op x x) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 x x X1
       have i₂ := eq870
       grind)
    | exact superpose eq870 eq32
    | exact resolve eq32 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq889 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq880 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq892 : ∀ X0 X1 : G, x = (M.op X0 (M.op x (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq883 X0 X1
       have i₂ := eq870
       grind)
    | exact superpose eq870 eq883
    | exact resolve eq883 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883
  have eq893 : ∀ X0 : G, x = (M.op (M.op X0 x) X0) := by
    intro X0
    first
    | (have i₁ := eq881 X0
       have i₂ := eq870
       grind)
    | exact superpose eq870 eq881
    | exact resolve eq881 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870 eq881
  have eq896 : ∀ X0 : G, x = (M.op (k X0 x) X0) := by
    intro X0
    first
    | (have i₁ := eq893 X0
       have i₂ := eq889 X0
       grind)
    | exact superpose eq889 eq893
    | exact resolve eq893 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq1051 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op x (M.op X1 (M.op X2 X1))) x)) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 (M.op x (M.op X1 (M.op X2 X1)))
       have i₂ := eq892 X2 X1
       grind)
    | exact superpose eq892 eq9
    | exact resolve eq9 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1052 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X0 X2)) X3) = (M.op X0 (M.op (M.op x (M.op X1 (M.op X2 X1))) x)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq31 X2 X3 X0 (M.op x (M.op X1 (M.op X2 X1)))
       have i₂ := eq892 X2 X1
       grind)
    | exact superpose eq892 eq31
    | exact resolve eq31 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq892
  have eq1071 : ∀ X0 X2 X3 : G, (M.op X0 X2) = (M.op (M.op X3 (M.op X0 X2)) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1052 X0 x X2 X3
       have i₂ := eq9 X2 x x
       grind)
    | exact superpose eq9 eq1052
    | exact resolve eq1052 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052
  have eq1072 : ∀ X0 X2 : G, (M.op (M.op X0 X2) X0) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq1051 X0 x X2
       have i₂ := eq9 X2 x x
       grind)
    | exact superpose eq9 eq1051
    | exact resolve eq1051 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051
  have eq1129 : ∀ X0 : G, (M.op x (k X0 x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1072 (k X0 x) X0
       have i₂ := eq896 X0
       grind)
    | exact superpose eq896 eq1072
    | exact resolve eq1072 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq1147 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 x X0
       have i₂ := eq1072 x (M.op X0 (M.op X1 X0))
       grind)
    | exact superpose eq1072 eq9
    | exact resolve eq9 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1199 : ∀ X0 : G, (τ (M.op (M.op X0 (M.op (σ x) (σ (M.op x x)))) X0)) = (M.op x (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq1129 (τ (M.op (M.op X0 (M.op (σ x) (σ (M.op x x)))) X0))
       have i₂ := eq728 X0
       grind)
    | exact superpose eq728 eq1129
    | exact resolve eq1129 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728 eq1129
  have eq1218 : ∀ X0 : G, x = (τ (M.op (M.op X0 (M.op (σ x) (σ (M.op x x)))) X0)) := by
    intro X0
    first
    | (have i₁ := eq1199 X0
       have i₂ := eq1147 x x
       grind)
    | exact superpose eq1147 eq1199
    | exact resolve eq1199 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147 eq1199
  have eq1222 : x = (τ (M.op (σ x) (σ (M.op x x)))) := by
    first
    | (have i₁ := eq1218 x
       have i₂ := eq1071 (σ x) (σ (M.op x x)) x
       grind)
    | exact superpose eq1071 eq1218
    | exact resolve eq1218 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071 eq1218
  have eq1224 : x = (τ (M.op (σ x) (σ (k x x)))) := by
    first
    | (have i₁ := eq1222
       have i₂ := eq889 x
       grind)
    | exact superpose eq889 eq1222
    | exact resolve eq1222 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1222
  have eq1225 : x = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq1224
       have i₂ := eq370 x
       grind)
    | exact superpose eq370 eq1224
    | exact resolve eq1224 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224
  have eq1426 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ x))
       have i₂ := eq1225
       grind)
    | exact superpose eq1225 eq11
    | exact resolve eq11 eq1225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1449 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq364
       have i₂ := eq1426
       grind)
    | exact superpose eq1426 eq364
    | exact resolve eq364 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364 eq1426
  have eq1475 : (σ x) ≠ (σ (k x x)) := by
    first
    | (have i₁ := eq1449
       have i₂ := eq889 x
       grind)
    | exact superpose eq889 eq1449
    | exact resolve eq1449 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889 eq1449
  have eq1479 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1475
       have i₂ := eq370 x
       grind)
    | exact superpose eq370 eq1475
    | exact resolve eq1475 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370 eq1475
  have eq1480 : False := by grind
  exact eq1480
