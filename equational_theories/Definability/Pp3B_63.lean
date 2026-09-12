import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_x_pxy_x_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq269 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq269 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq272 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq270 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq270 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq270 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq283 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq272 (σ X0)
       grind)
    | exact superpose eq272 eq15
    | exact resolve eq15 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq283 X0
       have i₂ := eq272 X0
       grind)
    | exact superpose eq272 eq283
    | exact resolve eq283 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272 eq283
  have eq348 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq302 X0
       grind)
    | exact superpose eq302 eq14
    | (have j0 := eq14 (σ X0) X1
       grind)
    | exact resolve eq14 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq302 X0
       grind)
    | exact superpose eq302 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq351 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq348 X0 X1
       have j1 := eq350 X0 X1
       grind)
    | (have r₁ := eq348 X0 X1
       have r₂ := eq350 X0 X1
       grind)
    | exact resolve eq348 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348 eq350
  have eq399 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq351 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq351
    | exact resolve eq351 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq351 x (σ y)
       grind)
    | exact superpose eq351 eq16
    | (have j1 := eq351 x (σ y)
       grind)
    | exact resolve eq16 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq422 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq403
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq403
    | exact resolve eq403 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq430 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq399 X0 X1
       grind)
    | exact superpose eq399 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq399 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq399 X0 X1
       grind)
    | exact resolve eq13 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq430 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq442 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq440 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq440 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq440 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq458 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq442 X0 (τ X1)
       grind)
    | exact superpose eq442 eq18
    | (have j1 := eq442 X0 (τ X1)
       grind)
    | exact resolve eq18 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq475 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq442 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1590 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq458 (τ X0) X1
       grind)
    | exact superpose eq458 eq17
    | (have j1 := eq458 (τ X0) X1
       grind)
    | exact resolve eq17 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq458
  have eq1597 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1590 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1590
    | (have j0 := eq1590 X0 X1
       grind)
    | exact resolve eq1590 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1590
  have eq1616 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1597 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1597
    | (have j0 := eq1597 X0 X1
       grind)
    | exact resolve eq1597 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1597
  have eq1621 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1616 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1616
    | (have j0 := eq1616 X0 X1
       grind)
    | exact resolve eq1616 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616
  have eq1686 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1621 X0 X1
       have i₂ := eq442 X0 X1
       grind)
    | exact superpose eq442 eq1621
    | (have j0 := eq1621 X0 X1
       have j1 := eq442 X0 X1
       grind)
    | exact resolve eq1621 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442 eq1621
  have eq1758 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1686 X0 X1
       have j1 := eq475 X0 X1
       grind)
    | (have r₁ := eq1686 X0 X1
       have r₂ := eq475 X0 X1
       grind)
    | exact resolve eq1686 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475 eq1686
  have eq1793 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1758 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1758
    | (have j0 := eq1758 X1 (σ X0)
       grind)
    | exact resolve eq1758 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1758
  have eq2502 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq1793 X1 (σ X0)
       grind)
    | exact superpose eq1793 eq28
    | (have j1 := eq1793 X1 (σ X0)
       grind)
    | exact resolve eq28 eq1793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1793
  have eq2516 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2502 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2502
    | (have j0 := eq2502 X0 X1
       grind)
    | exact resolve eq2502 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2502
  have eq2531 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2516 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2516
    | (have j0 := eq2516 X0 X1
       grind)
    | exact resolve eq2516 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2516
  have eq2540 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2531 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2531
    | (have j0 := eq2531 X0 X1
       grind)
    | exact resolve eq2531 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2531
  have eq2564 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2540 x y
       grind)
    | exact superpose eq2540 eq16
    | (have j1 := eq2540 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2540 x y
       grind)
    | exact resolve eq16 eq2540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2540
  have eq2602 : x = (k x y) := by grind
  clear eq2564
  have eq2908 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq422
       have i₂ := eq399 x y
       grind)
    | exact superpose eq399 eq422
    | (have j1 := eq399 x y
       grind)
    | exact resolve eq422 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2909 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq2908
  have eq2911 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq2909
       have i₂ := eq2602
       grind)
    | exact superpose eq2602 eq2909
    | exact resolve eq2909 eq2602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2909
  have eq2913 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2911
       have i₂ := eq2602
       grind)
    | exact superpose eq2602 eq2911
    | exact resolve eq2911 eq2602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2911
  have eq2915 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq422
       have i₂ := eq2913
       grind)
    | exact superpose eq2913 eq422
    | exact resolve eq422 eq2913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422 eq2913
  have eq2928 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2915
  have eq2929 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2928
       have i₂ := eq2602
       grind)
    | exact superpose eq2602 eq2928
    | exact resolve eq2928 eq2602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2928
  have eq2930 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2929
  have eq2932 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2930
       grind)
    | exact superpose eq2930 eq16
    | exact resolve eq16 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2930
  have eq2966 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq2932
       have i₂ := eq399 x y
       grind)
    | exact superpose eq399 eq2932
    | (have j1 := eq399 x y
       grind)
    | exact resolve eq2932 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq2967 : (M.op x y) = (k x y) := by grind
  clear eq2966
  have eq2970 : x = (M.op x y) := by
    first
    | (have i₁ := eq2967
       have i₂ := eq2602
       grind)
    | exact superpose eq2602 eq2967
    | exact resolve eq2967 eq2602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2602 eq2967
  have eq2972 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2932
       have i₂ := eq2970
       grind)
    | exact superpose eq2970 eq2932
    | exact resolve eq2932 eq2970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2932 eq2970
  have eq2987 : False := by grind
  exact eq2987

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_pyx_y_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq268 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq268 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq275 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq274 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq377 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq275 (σ y) (σ x)
       grind)
    | exact superpose eq275 eq16
    | (have j1 := eq275 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq275 X1 X0
       grind)
    | exact superpose eq275 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq275 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq275 X0 X1
       grind)
    | exact resolve eq13 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq379 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq387 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq386 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq386 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq386 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq388 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq377
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq377
    | exact resolve eq377 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq413 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq387 X0 (τ X1)
       grind)
    | exact superpose eq387 eq17
    | (have j1 := eq387 X0 (τ X1)
       grind)
    | exact resolve eq17 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq419 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq387 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq970 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq413 (τ X0) X1
       grind)
    | exact superpose eq413 eq18
    | (have j1 := eq413 (τ X0) X1
       grind)
    | exact resolve eq18 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq413
  have eq975 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq970 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq970
    | (have j0 := eq970 X0 X1
       grind)
    | exact resolve eq970 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq990 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq975 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq975
    | (have j0 := eq975 X0 X1
       grind)
    | exact resolve eq975 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq993 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq990 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq990
    | (have j0 := eq990 X0 X1
       grind)
    | exact resolve eq990 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq1058 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq993 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq993
    | (have j0 := eq993 X1 (σ X0)
       grind)
    | exact resolve eq993 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq1462 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1058 X0 X0
       have i₂ := eq387 X0 (σ X0)
       grind)
    | exact superpose eq387 eq1058
    | (have j0 := eq1058 X1 X0
       have j1 := eq387 X0 (σ X1)
       grind)
    | exact resolve eq1058 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387 eq1058
  have eq1497 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1462 X0 X1
       have j1 := eq419 (σ X1) X0
       grind)
    | (have r₁ := eq1462 X1 X1
       have r₂ := eq419 (σ X1) X1
       grind)
    | exact resolve eq1462 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq1462
  have eq1591 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq1497 (σ X0) X1
       grind)
    | exact superpose eq1497 eq22
    | (have j1 := eq1497 (σ X0) X1
       grind)
    | exact resolve eq22 eq1497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1497
  have eq1598 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1591 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1591
    | (have j0 := eq1591 X0 X1
       grind)
    | exact resolve eq1591 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1591
  have eq1614 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1598 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1598
    | (have j0 := eq1598 X0 X1
       grind)
    | exact resolve eq1598 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598
  have eq1623 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1614 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1614
    | (have j0 := eq1614 X0 X1
       grind)
    | exact resolve eq1614 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1614
  have eq1708 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1623 x y
       grind)
    | exact superpose eq1623 eq16
    | (have j1 := eq1623 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1623 x y
       grind)
    | exact resolve eq16 eq1623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623
  have eq1730 : x = (k y x) := by grind
  clear eq1708
  have eq2009 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq388
       have i₂ := eq275 y x
       grind)
    | exact superpose eq275 eq388
    | (have j1 := eq275 y x
       grind)
    | exact resolve eq388 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2012 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq2009
  have eq2013 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq2012
       have i₂ := eq1730
       grind)
    | exact superpose eq1730 eq2012
    | exact resolve eq2012 eq1730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2012
  have eq2014 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2013
       have i₂ := eq1730
       grind)
    | exact superpose eq1730 eq2013
    | exact resolve eq2013 eq1730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2013
  have eq2015 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq388
       have i₂ := eq2014
       grind)
    | exact superpose eq2014 eq388
    | exact resolve eq388 eq2014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388 eq2014
  have eq2029 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2015
  have eq2030 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2029
       have i₂ := eq1730
       grind)
    | exact superpose eq1730 eq2029
    | exact resolve eq2029 eq1730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2029
  have eq2031 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2030
  have eq2033 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2031
       grind)
    | exact superpose eq2031 eq16
    | exact resolve eq16 eq2031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2031
  have eq2067 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq2033
       have i₂ := eq275 y x
       grind)
    | exact superpose eq275 eq2033
    | (have j1 := eq275 y x
       grind)
    | exact resolve eq2033 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq2070 : (M.op x y) = (k y x) := by grind
  clear eq2067
  have eq2072 : x = (M.op x y) := by
    first
    | (have i₁ := eq2070
       have i₂ := eq1730
       grind)
    | exact superpose eq1730 eq2070
    | exact resolve eq2070 eq1730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1730 eq2070
  have eq2073 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2033
       have i₂ := eq2072
       grind)
    | exact superpose eq2072 eq2033
    | exact resolve eq2033 eq2072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2033 eq2072
  have eq2089 : False := by grind
  exact eq2089

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pyx_pxy_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq15
    | exact resolve eq15 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq66
    | exact resolve eq66 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq66
  have eq93 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2658 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | (have i₁ := eq77 X0
       have i₂ := eq14 (σ X0) (σ X0)
       grind)
    | exact superpose eq14 eq77
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq77 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq2670 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2658 X0 X1
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq2658 X0 X1
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq2658 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq2658
  have eq2691 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2670 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2670
    | exact resolve eq2670 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2670
  have eq2759 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq2691 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq2691 X0 X1
       grind)
    | exact superpose eq2691 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq2691 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq2691 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq2691 X0 X1
       grind)
    | exact resolve eq13 eq2691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2691
  have eq2770 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2759 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2759
  have eq2771 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2770 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2770
  have eq2775 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2771 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq2771 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq2771 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq2771 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2771
  have eq2817 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2775 (σ X0) (σ X1)
       grind)
    | exact superpose eq2775 eq15
    | exact resolve eq15 eq2775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2936 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2817 X0 X1
       have i₂ := eq2775 X0 X1
       grind)
    | exact superpose eq2775 eq2817
    | exact resolve eq2817 eq2775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2775 eq2817
  have eq4103 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2936 x y
       grind)
    | exact superpose eq2936 eq16
    | (have r₁ := eq16
       have r₂ := eq2936 x y
       grind)
    | exact resolve eq16 eq2936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2936
  have eq4121 : False := by grind
  exact eq4121

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_y_pxy_y_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq15
    | exact resolve eq15 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq66
    | exact resolve eq66 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq66
  have eq89 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq430 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq430
    | (have j0 := eq430 (σ X0) (σ X1)
       grind)
    | exact resolve eq430 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq431 X0 X1
       have i₂ := eq430 X0 X1
       grind)
    | exact superpose eq430 eq431
    | (have j0 := eq431 X0 X1
       have j1 := eq430 (σ X0) (σ X1)
       grind)
    | exact resolve eq431 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5856 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq460 x y
       grind)
    | exact superpose eq460 eq16
    | (have j1 := eq460 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq460 x y
       grind)
    | exact resolve eq16 eq460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq5882 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5856
  have eq5921 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5882
       grind)
    | exact superpose eq5882 eq16
    | exact resolve eq16 eq5882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5925 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq5882
       grind)
    | exact superpose eq5882 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq5882
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq5882
       grind)
    | exact resolve eq13 eq5882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5928 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5925
  have eq5932 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5928
       have i₂ := eq77 y
       grind)
    | exact superpose eq77 eq5928
    | exact resolve eq5928 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5928
  have eq5938 : (σ y) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5932
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq5932
    | exact resolve eq5932 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5932
  have eq5941 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq430 eq5938
    | (have j1 := eq430 x y
       grind)
    | exact resolve eq5938 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5938
  have eq5942 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq5941
       have r₂ := eq5921
       grind)
    | exact resolve eq5941 eq5921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5941
  have eq5947 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq89 y (σ x)
       have i₂ := eq5942
       grind)
    | exact superpose eq5942 eq89
    | (have j0 := eq89 y (σ x)
       grind)
    | (have r₁ := eq89 y (σ x)
       have r₂ := eq5942
       grind)
    | exact resolve eq89 eq5942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq5942
  have eq5955 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5947
  have eq5959 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5955
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq5955
    | exact resolve eq5955 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5955
  have eq5965 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5882 eq5959
    | exact resolve eq5959 eq5882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5882 eq5959
  have eq5969 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq430 eq5965
    | (have j1 := eq430 x y
       grind)
    | exact resolve eq5965 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq5965
  have eq5971 : y = (M.op x y) := by
    first
    | (have r₁ := eq5969
       have r₂ := eq5921
       grind)
    | exact resolve eq5969 eq5921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5921 eq5969
  have eq5972 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5971
       grind)
    | exact superpose eq5971 eq16
    | exact resolve eq16 eq5971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5973 : y = (M.op y (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq5971
       grind)
    | exact superpose eq5971 eq9
    | exact resolve eq9 eq5971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5975 : y ≠ y ∨ (M.op y y) = (M.op y x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq5971
       grind)
    | exact superpose eq5971 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq5971
       grind)
    | exact resolve eq13 eq5971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5978 : (M.op y y) = (M.op y x) ∨ y = (k x y) := by grind
  clear eq5975
  have eq5981 : y = (M.op y y) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq5973
       grind)
    | exact superpose eq5973 eq9
    | exact resolve eq9 eq5973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5973
  have eq6043 : y = (k x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq5978
       have i₂ := eq5981
       grind)
    | exact superpose eq5981 eq5978
    | exact resolve eq5978 eq5981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5978
  have eq6046 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq431 x y
       have i₂ := eq6043
       grind)
    | exact superpose eq6043 eq431
    | (have j0 := eq431 x y
       grind)
    | exact resolve eq431 eq6043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431 eq6043
  have eq6057 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq6046
  have eq6061 : y = (M.op y x) := by
    first
    | (have r₁ := eq6057
       have r₂ := eq5972
       grind)
    | exact resolve eq6057 eq5972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6057
  have eq6063 : x = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq9 x y
       have i₂ := eq6061
       grind)
    | exact superpose eq6061 eq9
    | exact resolve eq9 eq6061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6061
  have eq6072 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq6063
       have i₂ := eq5971
       grind)
    | exact superpose eq5971 eq6063
    | exact resolve eq6063 eq5971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6063
  have eq6075 : x = (M.op x y) := by
    first
    | (have i₁ := eq6072
       have i₂ := eq5971
       grind)
    | exact superpose eq5971 eq6072
    | exact resolve eq6072 eq5971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6072
  have eq6081 : x = y := by
    first
    | (have i₁ := eq5971
       have i₂ := eq6075
       grind)
    | exact superpose eq6075 eq5971
    | exact resolve eq5971 eq6075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5971 eq6075
  have eq6102 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5972
       have i₂ := eq6081
       grind)
    | exact superpose eq6081 eq5972
    | exact resolve eq5972 eq6081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5972
  have eq6103 : x = (M.op x x) := by
    first
    | (have i₁ := eq5981
       have i₂ := eq6081
       grind)
    | exact superpose eq6081 eq5981
    | exact resolve eq5981 eq6081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5981 eq6081
  have eq6106 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq6102
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq6102
    | exact resolve eq6102 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq6102
  have eq6159 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq6106
       have i₂ := eq6103
       grind)
    | exact superpose eq6103 eq6106
    | exact resolve eq6106 eq6103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6103 eq6106
  have eq6160 : False := by grind
  exact eq6160

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxy_pyx_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq86 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq178 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq86 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq86 X0 X1
       grind)
    | exact superpose eq86 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq86 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq86 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq86 X0 X1
       grind)
    | exact resolve eq13 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq86 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq86 X0 X1
       grind)
    | exact superpose eq86 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq86 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq86 X0 X1
       grind)
    | exact resolve eq12 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq183 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq178 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq188 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq179 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq179 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq179 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq189 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq183 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq183 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq183 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq183 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq198 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq188 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq188
    | (have j0 := eq188 X0 X1
       grind)
    | exact resolve eq188 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq199 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq198 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq200 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq189 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq189
    | (have j0 := eq189 X0 X1
       grind)
    | exact resolve eq189 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq201 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq200 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq206 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq201 X0 X1
       have j1 := eq199 X0 X1
       grind)
    | (have r₁ := eq201 X0 X1
       have r₂ := eq199 X0 X1
       grind)
    | exact resolve eq201 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq201
  have eq207 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq206 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq206
    | exact resolve eq206 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq206 x y
       grind)
    | exact superpose eq206 eq16
    | exact resolve eq16 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq273 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq207 X0 (τ X1)
       grind)
    | exact superpose eq207 eq18
    | exact resolve eq18 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq207
  have eq290 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq273 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq273
    | exact resolve eq273 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq298 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq290 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq290
    | exact resolve eq290 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq318 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq218
       have i₂ := eq298 x y
       grind)
    | exact superpose eq298 eq218
    | exact resolve eq218 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq298
  have eq319 : False := by grind
  exact eq319

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_pyy_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq32 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X0))) ≠ X0 ∨ (M.op (M.op X0 (M.op X0 (M.op X1 X0))) X0) = (k (M.op X0 (M.op X0 (M.op X1 X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 (M.op X0 (M.op X1 X0))) X0
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X0 (M.op X0 (M.op X1 X0))) X0
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq80 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
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
  have eq139 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq3908 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq80 X0 X1
       grind)
    | exact superpose eq80 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq80 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) X1
       have r₂ := eq80 X0 X1
       grind)
    | (have r₁ := eq12 X1 (σ X0)
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq12 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3930 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq80 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq3931 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq3930 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3930
  have eq3934 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq3908 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3908
  have eq3936 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3931 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3931
    | (have j0 := eq3931 X0
       grind)
    | exact resolve eq3931 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3931
  have eq4028 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3936 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3936
    | exact resolve eq3936 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3936
  have eq4062 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4028 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq4028
    | (have j0 := eq4028 X0
       grind)
    | exact resolve eq4028 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4028
  have eq4064 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq4062 X0
       grind)
    | exact superpose eq4062 eq9
    | (have j1 := eq4062 X0
       grind)
    | exact resolve eq9 eq4062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4062
  have eq8757 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = (M.op X0 X0) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq4064 X0
       grind)
    | exact superpose eq4064 eq32
    | (have j1 := eq4064 X0
       grind)
    | (have r₁ := eq32 X0 X0
       have r₂ := eq4064 X0
       grind)
    | exact resolve eq32 eq4064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq4064
  have eq8779 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq8757 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8757
  have eq9002 : ∀ X0 : G, (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) ∨ (τ (k (σ X0) (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (σ X0)
       have i₂ := eq8779 (σ X0)
       grind)
    | exact superpose eq8779 eq29
    | (have j1 := eq8779 (σ X0)
       grind)
    | exact resolve eq29 eq8779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq8779
  have eq9068 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (τ (k (σ X0) (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq9002 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9002
    | (have j0 := eq9002 X0
       grind)
    | exact resolve eq9002 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9002
  have eq9122 : ∀ X0 : G, (k (τ (σ X0)) X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq9068 X0
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq9068
    | (have j0 := eq9068 X0
       grind)
    | exact resolve eq9068 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq9068
  have eq9165 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq9122 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9122
    | (have j0 := eq9122 X0
       grind)
    | exact resolve eq9122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9122
  have eq9166 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq9165 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9165
  have eq9189 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9166 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9166
    | exact resolve eq9166 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9231 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq9166 X0
       grind)
    | exact superpose eq9166 eq11
    | exact resolve eq11 eq9166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9166
  have eq9325 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9189 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq9189
    | exact resolve eq9189 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9189
  have eq9492 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq9325 X0
       grind)
    | exact superpose eq9325 eq11
    | exact resolve eq11 eq9325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9617 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq9492 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq9492
    | exact resolve eq9492 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9492
  have eq9710 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq9617 (τ X0)
       grind)
    | exact superpose eq9617 eq33
    | exact resolve eq33 eq9617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq9770 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9710 X0
       have i₂ := eq9325 X0
       grind)
    | exact superpose eq9325 eq9710
    | exact resolve eq9710 eq9325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9325 eq9710
  have eq212591 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) X1)
       have i₂ := eq3934 X0 X1
       grind)
    | exact superpose eq3934 eq11
    | (have j1 := eq3934 X0 X1
       grind)
    | exact resolve eq11 eq3934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3934
  have eq212759 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq212591 X0 X1
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq212591
    | (have j0 := eq212591 X0 X1
       grind)
    | exact resolve eq212591 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212591
  have eq212760 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq212759 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212759
  have eq213647 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq212760 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq212760
    | exact resolve eq212760 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213823 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq212760 x (σ y)
       grind)
    | exact superpose eq212760 eq16
    | (have j1 := eq212760 x (σ y)
       grind)
    | exact resolve eq16 eq212760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212760
  have eq213946 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq213823
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq213823
    | exact resolve eq213823 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213823
  have eq214215 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq213647 X1 X0
       grind)
    | exact superpose eq213647 eq9
    | (have j1 := eq213647 X1 X0
       grind)
    | exact resolve eq9 eq213647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214216 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq213647 X1 X0
       grind)
    | exact superpose eq213647 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq213647 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq213647 X0 X1
       grind)
    | exact resolve eq12 eq213647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214217 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq213647 X1 X0
       grind)
    | exact superpose eq213647 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq213647 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq213647 X0 X1
       grind)
    | exact resolve eq13 eq213647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214581 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq214217 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214217
  have eq214582 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq214216 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214216
  have eq214709 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq214581 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq214581 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq214581 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214581
  have eq217112 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq214709 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq214709
    | exact resolve eq214709 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217725 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq214709 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214709
  have eq218056 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (k X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq217112 X0 X1
       have i₂ := eq9231 X1
       grind)
    | exact superpose eq9231 eq217112
    | (have j0 := eq217112 X0 X1
       grind)
    | exact resolve eq217112 eq9231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217112
  have eq218309 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq218056 X0 X1
       have i₂ := eq9617 X1
       grind)
    | exact superpose eq9617 eq218056
    | (have j0 := eq218056 X0 X1
       grind)
    | exact resolve eq218056 eq9617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218056
  have eq219820 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq214215 X0 X1
       grind)
    | exact superpose eq214215 eq9
    | (have j1 := eq214215 X0 X1
       grind)
    | exact resolve eq9 eq214215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214215
  have eq220442 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ X0 ∨ (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq217725 X0 X0
       have i₂ := eq219820 X0 X1
       grind)
    | exact superpose eq219820 eq217725
    | (have j1 := eq219820 X0 X2
       grind)
    | exact resolve eq217725 eq219820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217725
  have eq220490 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9231 X0
       have i₂ := eq219820 (σ X0) X1
       grind)
    | exact superpose eq219820 eq9231
    | (have j1 := eq219820 (σ X0) X1
       grind)
    | exact resolve eq9231 eq219820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220515 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9770 X0
       have i₂ := eq219820 (τ X0) X1
       grind)
    | exact superpose eq219820 eq9770
    | (have j1 := eq219820 (τ X0) X1
       grind)
    | exact resolve eq9770 eq219820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9770
  have eq220563 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq220490 X0 X1
       have i₂ := eq9617 X0
       grind)
    | exact superpose eq9617 eq220490
    | (have j0 := eq220490 X0 X1
       grind)
    | exact resolve eq220490 eq9617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220490
  have eq225257 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq220515 X0 X1
       grind)
    | exact superpose eq220515 eq11
    | (have j1 := eq220515 X0 X1
       grind)
    | exact resolve eq11 eq220515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220515
  have eq225482 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq225257 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq225257
    | (have j0 := eq225257 X0 X1
       grind)
    | exact resolve eq225257 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225257
  have eq226527 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9231 X0
       have i₂ := eq225482 (σ X0) X1
       grind)
    | exact superpose eq225482 eq9231
    | (have j1 := eq225482 (σ X0) X1
       grind)
    | exact resolve eq9231 eq225482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9231 eq225482
  have eq226599 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq226527 X0 X1
       have i₂ := eq9617 X0
       grind)
    | exact superpose eq9617 eq226527
    | (have j0 := eq226527 X0 X1
       grind)
    | exact resolve eq226527 eq9617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9617 eq226527
  have eq226670 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq226599 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq226599
    | (have j0 := eq226599 X0 X1
       grind)
    | exact resolve eq226599 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226599
  have eq230404 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq220442 X0 X1 X2
       have i₂ := eq213647 X1 X0
       grind)
    | exact superpose eq213647 eq220442
    | (have j0 := eq220442 X0 X1 X2
       have j1 := eq213647 X2 X0
       grind)
    | (have r₁ := eq220442 X1 X0 X2
       have r₂ := eq213647 X0 X1
       grind)
    | exact resolve eq220442 eq213647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220442
  have eq230688 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X2 X0) ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq230404 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230404
  have eq290258 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq218309 x y
       grind)
    | exact superpose eq218309 eq16
    | (have j1 := eq218309 x y
       grind)
    | exact resolve eq16 eq218309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218309
  have eq296911 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq230688 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230688
  have eq296912 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq296911 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296911
  have eq297378 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq296912 (τ X0) X1
       grind)
    | exact superpose eq296912 eq17
    | (have j1 := eq296912 (τ X0) X1
       grind)
    | exact resolve eq17 eq296912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq297596 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq296912 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296912
  have eq304344 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq297378 X1 (τ X0)
       grind)
    | exact superpose eq297378 eq18
    | (have j1 := eq297378 X1 (τ X0)
       grind)
    | exact resolve eq18 eq297378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq297378
  have eq304505 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq304344 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq304344
    | (have j0 := eq304344 X0 X1
       grind)
    | exact resolve eq304344 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304344
  have eq304815 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq304505 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq304505
    | (have j0 := eq304505 X0 X1
       grind)
    | exact resolve eq304505 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304505
  have eq305044 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq304815 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq304815
    | (have j0 := eq304815 X0 X1
       grind)
    | exact resolve eq304815 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304815
  have eq308926 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq305044 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq305044
    | (have j0 := eq305044 X1 (σ X0)
       grind)
    | exact resolve eq305044 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305044
  have eq321437 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq308926 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq308926
    | (have j0 := eq308926 X1 (σ X0)
       grind)
    | exact resolve eq308926 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308926
  have eq322197 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq321437 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq321437
    | (have j0 := eq321437 X0 X1
       grind)
    | exact resolve eq321437 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321437
  have eq322339 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq322197 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq322197
    | (have j0 := eq322197 X0 X1
       grind)
    | exact resolve eq322197 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322197
  have eq326341 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq290258
       have i₂ := eq322339 y x
       grind)
    | exact superpose eq322339 eq290258
    | (have j1 := eq322339 y x
       grind)
    | (have r₁ := eq290258
       have r₂ := eq322339 y x
       grind)
    | exact resolve eq290258 eq322339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq326343 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq135
       have i₂ := eq322339 y x
       grind)
    | exact superpose eq322339 eq135
    | (have j1 := eq322339 y x
       grind)
    | (have r₁ := eq135
       have r₂ := eq322339 y x
       grind)
    | exact resolve eq135 eq322339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq326751 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq322339 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322339
  have eq326752 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq326343
  have eq326754 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq326341
  have eq326876 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq139 y x
       grind)
    | (have r₁ := eq326752
       have r₂ := eq139 x y
       grind)
    | exact resolve eq326752 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq326752
  have eq330444 : ∀ X0 : G, (σ (M.op x y)) = (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (σ (k x y)) := by
    intro X0
    first
    | (have i₁ := eq220563 y X0
       have i₂ := eq326754
       grind)
    | exact superpose eq326754 eq220563
    | (have j0 := eq220563 y X0
       grind)
    | exact resolve eq220563 eq326754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220563 eq326754
  have eq330982 : ∀ X0 : G, (σ y) = (σ (k x y)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq330444 X0
       have j1 := eq326751 x y
       grind)
    | (have r₁ := eq330444 X0
       have r₂ := eq326751 x y
       grind)
    | exact resolve eq330444 eq326751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326751 eq330444
  have eq337241 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq297596 (σ y) (σ x)
       have i₂ := eq326876
       grind)
    | exact superpose eq326876 eq297596
    | (have j0 := eq297596 (σ y) (σ x)
       grind)
    | (have r₁ := eq297596 (σ y) (σ x)
       have r₂ := eq326876
       grind)
    | (have r₁ := eq297596 (σ x) (σ y)
       have r₂ := eq326876
       grind)
    | exact resolve eq297596 eq326876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297596 eq326876
  have eq337244 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq337241
  have eq337254 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq337244
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq337244
    | exact resolve eq337244 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337244
  have eq340162 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq337254
       grind)
    | exact superpose eq337254 eq16
    | exact resolve eq16 eq337254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337254
  have eq340324 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq340162
       have i₂ := eq213647 x y
       grind)
    | exact superpose eq213647 eq340162
    | (have j1 := eq213647 x y
       grind)
    | exact resolve eq340162 eq213647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213647
  have eq340325 : (M.op x y) = (k x y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq340324
  have eq346237 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq290258
       have i₂ := eq340325
       grind)
    | exact superpose eq340325 eq290258
    | exact resolve eq290258 eq340325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340325
  have eq346272 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq346237
  have eq349550 : ∀ X0 : G, (k x y) = (τ (σ y)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq330982 X0
       grind)
    | exact superpose eq330982 eq10
    | (have j1 := eq330982 X0
       grind)
    | exact resolve eq10 eq330982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330982
  have eq350063 : ∀ X0 : G, y = (k x y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq349550 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq349550
    | (have j0 := eq349550 X0
       grind)
    | exact resolve eq349550 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349550
  have eq361464 : ∀ X0 : G, (σ (M.op x y)) = (σ y) ∨ (k X0 y) = (M.op X0 y) ∨ (σ x) = (σ (k y x)) := by
    intro X0
    first
    | (have i₁ := eq226670 y X0
       have i₂ := eq346272
       grind)
    | exact superpose eq346272 eq226670
    | (have j0 := eq226670 y X0
       grind)
    | exact resolve eq226670 eq346272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226670 eq346272
  have eq361997 : ∀ X0 : G, (σ x) = (σ (k y x)) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq361464 X0
       grind)
    | (have r₁ := eq361464 X0
       have r₂ := eq340162
       grind)
    | exact resolve eq361464 eq340162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340162 eq361464
  have eq364833 : ∀ X0 : G, (τ (σ x)) = (k y x) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq361997 X0
       grind)
    | exact superpose eq361997 eq10
    | (have j1 := eq361997 X0
       grind)
    | exact resolve eq10 eq361997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361997
  have eq365363 : ∀ X0 : G, x = (k y x) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq364833 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq364833
    | (have j0 := eq364833 X0
       grind)
    | exact resolve eq364833 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364833
  have eq365579 : ∀ X0 : G, x = (M.op y x) ∨ (M.op x y) = (k x y) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq214582 y x
       have i₂ := eq365363 X0
       grind)
    | exact superpose eq365363 eq214582
    | (have j0 := eq214582 x y
       have j1 := eq365363 x
       grind)
    | exact resolve eq214582 eq365363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214582 eq365363
  have eq365599 : ∀ X0 : G, (M.op x y) = (k x y) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq365579 x
       have j1 := eq12 x y
       grind)
    | (have r₁ := eq365579 X0
       have r₂ := eq12 x y
       grind)
    | exact resolve eq365579 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365579
  have eq368206 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have j0 := eq365599 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365599
  have eq368207 : (M.op x y) = (k x y) := by grind
  clear eq368206
  have eq368223 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq290258
       have i₂ := eq368207
       grind)
    | exact superpose eq368207 eq290258
    | exact resolve eq290258 eq368207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290258
  have eq368229 : ∀ X0 : G, y = (M.op x y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq350063 X0
       have i₂ := eq368207
       grind)
    | exact superpose eq368207 eq350063
    | (have j0 := eq350063 X0
       grind)
    | exact resolve eq350063 eq368207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350063
  have eq368262 : (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq368223
  have eq370665 : (M.op y y) = (τ (σ (M.op x y))) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq368262
       grind)
    | exact superpose eq368262 eq10
    | exact resolve eq10 eq368262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368262
  have eq371190 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq370665
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq370665
    | exact resolve eq370665 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370665
  have eq371402 : ∀ X0 : G, y = (M.op x y) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq219820 y X0
       have i₂ := eq371190
       grind)
    | exact superpose eq371190 eq219820
    | (have j0 := eq219820 y X0
       grind)
    | exact resolve eq219820 eq371190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219820 eq371190
  have eq373894 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq213946
       have i₂ := eq371402 X0
       grind)
    | exact superpose eq371402 eq213946
    | (have j1 := eq371402 X0
       grind)
    | exact resolve eq213946 eq371402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371402
  have eq373935 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq373894 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373894
  have eq373943 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq373935 X0
       have i₂ := eq368207
       grind)
    | exact superpose eq368207 eq373935
    | (have j0 := eq373935 X0
       grind)
    | exact resolve eq373935 eq368207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368207 eq373935
  have eq373946 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq373943 X0
       grind)
    | (have r₁ := eq373943 X0
       have r₂ := eq16
       grind)
    | exact resolve eq373943 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373943
  have eq404948 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq213946
       have i₂ := eq368229 X0
       grind)
    | exact superpose eq368229 eq213946
    | (have j1 := eq368229 X0
       grind)
    | exact resolve eq213946 eq368229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213946 eq368229
  have eq404989 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq404948 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404948
  have eq404994 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq404989 X0
       have i₂ := eq373946 x
       grind)
    | exact superpose eq373946 eq404989
    | (have j0 := eq404989 X0
       grind)
    | exact resolve eq404989 eq373946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404989
  have eq404997 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq404994 X0
       grind)
    | (have r₁ := eq404994 X0
       have r₂ := eq16
       grind)
    | exact resolve eq404994 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404994
  have eq408065 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq404997 (σ X0)
       grind)
    | exact superpose eq404997 eq15
    | exact resolve eq15 eq404997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404997
  have eq408452 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq408065 X0
       have i₂ := eq373946 X0
       grind)
    | exact superpose eq373946 eq408065
    | exact resolve eq408065 eq373946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373946 eq408065
  have eq409282 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq408452 x
       grind)
    | exact superpose eq408452 eq16
    | (have r₁ := eq16
       have r₂ := eq408452 x
       grind)
    | exact resolve eq16 eq408452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408452
  have eq409413 : False := by grind
  exact eq409413

/-- `Equation4167`: `x ◇ y = ((y ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation4167 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4167 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4167.models_iff G M).mp hM
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
  have eq98 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq311 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq98 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq98 X0 X1
       grind)
    | exact superpose eq98 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq98 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq98 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq98 X1 X1
       grind)
    | exact resolve eq13 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq98 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq314 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq311 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq315 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq314 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq318 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq315 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq315
    | (have j0 := eq315 X0 X1
       grind)
    | exact resolve eq315 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq322 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq318 X0 X1
       have j1 := eq313 X0 X1
       grind)
    | (have r₁ := eq318 X0 X1
       have r₂ := eq313 X0 X1
       grind)
    | (have r₁ := eq318 X0 (k X1 X0)
       have r₂ := eq313 X0 X1
       grind)
    | (have r₁ := eq318 X0 X0
       have r₂ := eq313 X0 X0
       grind)
    | exact resolve eq318 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq318
  have eq642 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq322 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq322
    | exact resolve eq322 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq656 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq322 x y
       grind)
    | exact superpose eq322 eq16
    | (have j1 := eq322 x y
       grind)
    | exact resolve eq16 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq673 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq642 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq642
    | (have j0 := eq642 X0 X1
       grind)
    | exact resolve eq642 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq642
  have eq674 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq673 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq673
    | exact resolve eq673 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq741 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq674 (τ X1) X0
       grind)
    | exact superpose eq674 eq18
    | (have j1 := eq674 (τ X1) X0
       grind)
    | exact resolve eq18 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq674
  have eq918 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq741 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq741
    | exact resolve eq741 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq967 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq918 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq918
    | (have j0 := eq918 X0 X1
       grind)
    | exact resolve eq918 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq1054 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq656
       have i₂ := eq967 y x
       grind)
    | exact superpose eq967 eq656
    | (have j1 := eq967 (σ y) (σ x)
       grind)
    | (have r₁ := eq656
       have r₂ := eq967 y x
       grind)
    | exact resolve eq656 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1055 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1054
  have eq1097 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1055
  have eq1107 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq656
       have i₂ := eq1097
       grind)
    | exact superpose eq1097 eq656
    | exact resolve eq656 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656 eq1097
  have eq1108 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1107
  have eq1109 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1108
  have eq1259 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1109
  have eq1271 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1259
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1259
    | exact resolve eq1259 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259
  have eq1277 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1271
       grind)
    | exact superpose eq1271 eq16
    | exact resolve eq16 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271
  have eq1286 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1277
       have i₂ := eq967 y x
       grind)
    | exact superpose eq967 eq1277
    | (have j1 := eq967 y x
       grind)
    | (have r₁ := eq1277
       have r₂ := eq967 y x
       grind)
    | exact resolve eq1277 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq1287 : y = (M.op x x) := by grind
  clear eq1286
  have eq1293 : (M.op x y) = (k y x) := by grind
  clear eq1287
  have eq1345 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1277
       have i₂ := eq1293
       grind)
    | exact superpose eq1293 eq1277
    | exact resolve eq1277 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277 eq1293
  have eq1348 : False := by grind
  exact eq1348

/-- `Equation4167`: `x ◇ y = ((y ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pyx_pxy_pyx_Equation4167 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4167 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4167.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X1 X1) X1) X0) := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq61 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X0) (M.op (M.op X0 X0) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq9 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq63 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op (M.op X0 X0) X0) X0) ∨ (M.op (M.op (M.op X0 X0) X0) X1) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq9 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X1 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op (M.op (M.op X0 X0) X0) X1) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 X1
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq63
    | (have j0 := eq63 X0 X1
       grind)
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X1 X0) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq64
    | (have j0 := eq64 X0 X1
       grind)
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq274 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq274 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq278 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq275 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq275 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq275 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq295 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq278 (σ X0)
       grind)
    | exact superpose eq278 eq15
    | exact resolve eq15 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq278 (τ X0)
       grind)
    | exact superpose eq278 eq31
    | exact resolve eq31 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq308 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq301 X0
       have i₂ := eq278 X0
       grind)
    | exact superpose eq278 eq301
    | exact resolve eq301 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq314 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq295 X0
       have i₂ := eq278 X0
       grind)
    | exact superpose eq278 eq295
    | exact resolve eq295 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq295
  have eq357 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq314 X0
       grind)
    | exact superpose eq314 eq14
    | (have j0 := eq14 X1 X1
       grind)
    | exact resolve eq14 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq314 X0
       grind)
    | exact superpose eq314 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op (M.op (σ (M.op X0 X0)) (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq314 X0
       grind)
    | exact superpose eq314 eq9
    | exact resolve eq9 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq357 X0 X1
       have j1 := eq359 X0 X1
       grind)
    | (have r₁ := eq357 X0 X1
       have r₂ := eq359 X0 X1
       grind)
    | exact resolve eq357 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq428 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq314 X0
       have i₂ := eq361 X1 (σ X0)
       grind)
    | exact superpose eq361 eq314
    | (have j1 := eq361 X1 (σ X0)
       grind)
    | exact resolve eq314 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq432 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq428 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq428
    | (have j0 := eq428 X0 X1
       grind)
    | exact resolve eq428 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq864 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq432 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq432
    | (have j0 := eq432 X1 X1
       grind)
    | exact resolve eq432 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq877 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq432 y x
       grind)
    | exact superpose eq432 eq16
    | (have j1 := eq432 y x
       grind)
    | exact resolve eq16 eq432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq909 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq864 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq864
    | (have j0 := eq864 X0 X1
       grind)
    | exact resolve eq864 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq864
  have eq932 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq909 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq909
    | exact resolve eq909 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq965 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq932 X0 X1
       have i₂ := eq308 X0
       grind)
    | exact superpose eq308 eq932
    | (have j0 := eq932 X0 X1
       grind)
    | exact resolve eq932 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq966 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq965 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq965
    | (have j0 := eq965 X0 X1
       grind)
    | exact resolve eq965 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq975 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X0 X0) X1) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq966 X0 X2
       grind)
    | exact superpose eq966 eq9
    | (have j1 := eq966 X0 X2
       grind)
    | exact resolve eq9 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq992 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq308 X0
       have i₂ := eq966 (τ X0) X1
       grind)
    | exact superpose eq966 eq308
    | (have j1 := eq966 (τ X0) X1
       grind)
    | exact resolve eq308 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308 eq966
  have eq1090 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq992 X0 X1
       grind)
    | exact superpose eq992 eq11
    | (have j1 := eq992 X0 X1
       grind)
    | exact resolve eq11 eq992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1104 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1090 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1090
    | (have j0 := eq1090 X0 X1
       grind)
    | exact resolve eq1090 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1135 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq1104 X1 X0
       grind)
    | exact superpose eq1104 eq17
    | (have j1 := eq1104 X1 X1
       grind)
    | exact resolve eq17 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1246 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq314 X0
       have i₂ := eq1135 X1 (σ X0)
       grind)
    | exact superpose eq1135 eq314
    | (have j1 := eq1135 X1 (σ X0)
       grind)
    | exact resolve eq314 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq1255 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1246 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1246
    | (have j0 := eq1246 X0 X1
       grind)
    | exact resolve eq1246 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246
  have eq1273 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1255 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1255
    | (have j0 := eq1255 X0 X1
       grind)
    | exact resolve eq1255 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255
  have eq3288 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq1273 X0 X1
       grind)
    | exact superpose eq1273 eq10
    | (have j1 := eq1273 X0 X1
       grind)
    | exact resolve eq10 eq1273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273
  have eq3370 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3288 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3288
    | (have j0 := eq3288 X0 X1
       grind)
    | exact resolve eq3288 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3288
  have eq3406 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X0 X0) X1) ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq3370 X0 X2
       grind)
    | exact superpose eq3370 eq9
    | (have j1 := eq3370 X0 X2
       grind)
    | exact resolve eq9 eq3370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3370
  have eq4929 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 (M.op X0 X0)) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X1 X1
       have i₂ := eq975 X1 X1 X2
       grind)
    | exact superpose eq975 eq65
    | (have j1 := eq975 X0 X1 X2
       grind)
    | (have r₁ := eq65 X0 X1
       have r₂ := eq975 X0 X0 X2
       grind)
    | exact resolve eq65 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4931 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 (M.op X0 X0)) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4929 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4929
  have eq5033 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq4931 X0 x (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4931
  have eq5034 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq5033 X0
       have j1 := eq975 X0 x (M.op X0 X0)
       grind)
    | (have r₁ := eq5033 X0
       have r₂ := eq975 X0 X0 x
       grind)
    | exact resolve eq5033 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975 eq5033
  have eq5069 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq5034 (σ X0)
       have i₂ := eq314 X0
       grind)
    | exact superpose eq314 eq5034
    | exact resolve eq5034 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq5098 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq5069 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq5069
    | exact resolve eq5069 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5069
  have eq5119 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5098 X0
       have i₂ := eq5034 X0
       grind)
    | exact superpose eq5034 eq5098
    | exact resolve eq5098 eq5034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5034 eq5098
  have eq5690 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op (σ (M.op (M.op X0 X0) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq360 X0 X1
       have i₂ := eq5119 X0
       grind)
    | exact superpose eq5119 eq360
    | exact resolve eq360 eq5119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360 eq5119
  have eq24960 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) X1) ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X0 X0)
       have i₂ := eq3406 X0 (M.op X0 X0) X2
       grind)
    | exact superpose eq3406 eq9
    | (have j1 := eq3406 X0 X1 X2
       grind)
    | exact resolve eq9 eq3406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3406
  have eq25091 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (M.op X1 (M.op X0 X0)) ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24960 X0 X1 X2
       have i₂ := eq9 (M.op X0 X0) X0
       grind)
    | exact superpose eq9 eq24960
    | (have j0 := eq24960 X0 X1 X2
       grind)
    | exact resolve eq24960 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24960
  have eq25140 : ∀ X0 X1 X2 : G, (σ (k X0 X2)) = (σ (M.op X2 X0)) ∨ (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25091 X0 X1 X2
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq25091
    | (have j0 := eq25091 X0 X1 X2
       grind)
    | exact resolve eq25091 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25091
  have eq33842 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (M.op X0 y) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq877
       have i₂ := eq25140 y X0 x
       grind)
    | exact superpose eq25140 eq877
    | (have j1 := eq25140 y X0 x
       grind)
    | (have r₁ := eq877
       have r₂ := eq25140 y x x
       grind)
    | exact resolve eq877 eq25140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877 eq25140
  have eq33938 : ∀ X0 : G, (σ y) = (σ (M.op y y)) ∨ (M.op X0 y) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq33842 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33842
  have eq34008 : ∀ X0 : G, (M.op y y) = (τ (σ y)) ∨ (M.op X0 y) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq33938 X0
       grind)
    | exact superpose eq33938 eq10
    | (have j1 := eq33938 X0
       grind)
    | exact resolve eq10 eq33938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33938
  have eq34158 : ∀ X0 : G, y = (M.op y y) ∨ (M.op X0 y) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq34008 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq34008
    | (have j0 := eq34008 X0
       grind)
    | exact resolve eq34008 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34008
  have eq34187 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op y y) X0) ∨ (M.op X1 (M.op y y)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq34158 X1
       grind)
    | exact superpose eq34158 eq9
    | (have j1 := eq34158 X1
       grind)
    | exact resolve eq9 eq34158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34158
  have eq41267 : (M.op (M.op y y) y) ≠ (M.op (M.op y y) y) ∨ (M.op (M.op y y) (M.op y y)) = (M.op (M.op y y) y) := by
    first
    | (have j0 := eq34187 (M.op y y) (M.op y y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34187
  have eq41268 : (M.op (M.op y y) (M.op y y)) = (M.op (M.op y y) y) := by grind
  clear eq41267
  have eq41400 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (M.op (M.op (M.op y y) y) (M.op y y)) X0) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op y y)
       have i₂ := eq41268
       grind)
    | exact superpose eq41268 eq9
    | exact resolve eq9 eq41268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41404 : ∀ X0 : G, (M.op X0 (M.op (M.op (M.op y y) y) (M.op y y))) = (M.op (M.op (M.op (M.op y y) y) (M.op (M.op (M.op y y) y) (M.op y y))) X0) := by
    intro X0
    first
    | (have i₁ := eq62 (M.op y y) x
       have i₂ := eq41268
       grind)
    | exact superpose eq41268 eq62
    | exact resolve eq62 eq41268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41462 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = (M.op (σ (M.op (M.op (M.op y y) y) (M.op y y))) X0) := by
    intro X0
    first
    | (have i₁ := eq5690 (M.op y y) X0
       have i₂ := eq41268
       grind)
    | exact superpose eq41268 eq5690
    | exact resolve eq5690 eq41268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41539 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = (M.op (σ (M.op (M.op y y) y)) X0) := by
    intro X0
    first
    | (have i₁ := eq41462 X0
       have i₂ := eq9 (M.op y y) y
       grind)
    | exact superpose eq9 eq41462
    | exact resolve eq41462 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41462
  have eq41565 : ∀ X0 : G, (M.op X0 (M.op (M.op (M.op y y) y) (M.op y y))) = (M.op (M.op (M.op (M.op (M.op y y) y) (M.op y y)) y) X0) := by
    intro X0
    first
    | (have i₁ := eq41404 X0
       have i₂ := eq9 (M.op (M.op (M.op y y) y) (M.op y y)) y
       grind)
    | exact superpose eq9 eq41404
    | exact resolve eq41404 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41404
  have eq41566 : ∀ X0 : G, (M.op (M.op (M.op y y) y) X0) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq41400 X0
       have i₂ := eq9 (M.op y y) y
       grind)
    | exact superpose eq9 eq41400
    | exact resolve eq41400 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41400
  have eq41582 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq41539 X0
       have i₂ := eq5690 y X0
       grind)
    | exact superpose eq5690 eq41539
    | exact resolve eq41539 eq5690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41539
  have eq41599 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = (M.op (M.op (M.op (M.op y y) y) y) X0) := by
    intro X0
    first
    | (have i₁ := eq41565 X0
       have i₂ := eq9 (M.op y y) y
       grind)
    | exact superpose eq9 eq41565
    | exact resolve eq41565 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41565
  have eq41600 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq41566 X0
       have i₂ := eq9 X0 y
       grind)
    | exact superpose eq9 eq41566
    | exact resolve eq41566 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41566
  have eq41604 : ∀ X0 : G, (M.op (M.op y y) X0) = (M.op X0 (M.op (M.op y y) y)) := by
    intro X0
    first
    | (have i₁ := eq41599 X0
       have i₂ := eq9 y y
       grind)
    | exact superpose eq9 eq41599
    | exact resolve eq41599 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41599
  have eq41763 : ∀ X0 : G, (M.op (M.op y y) (M.op y y)) ≠ (M.op (M.op (M.op y y) (M.op y y)) y) ∨ (M.op X0 (M.op y y)) = (k X0 (M.op (M.op (M.op y y) (M.op y y)) y)) := by
    intro X0
    first
    | (have i₁ := eq65 (M.op y y) x
       have i₂ := eq41600 (M.op (M.op y y) (M.op y y))
       grind)
    | exact superpose eq41600 eq65
    | exact resolve eq65 eq41600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq41773 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = (M.op (σ (M.op (M.op (M.op y y) (M.op y y)) y)) X0) := by
    intro X0
    first
    | (have i₁ := eq5690 (M.op y y) X0
       have i₂ := eq41600 (M.op (M.op y y) (M.op y y))
       grind)
    | exact superpose eq41600 eq5690
    | exact resolve eq5690 eq41600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5690
  have eq41782 : ∀ X0 : G, (M.op (M.op y y) X0) = (M.op (M.op (M.op X0 X0) X0) y) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op y y) X0
       have i₂ := eq41600 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq41600 eq9
    | exact resolve eq9 eq41600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41865 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y y) X0) := by
    intro X0
    first
    | (have i₁ := eq41782 X0
       have i₂ := eq9 y X0
       grind)
    | exact superpose eq9 eq41782
    | exact resolve eq41782 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41782
  have eq41873 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = (M.op (σ (M.op (M.op (M.op y y) y) y)) X0) := by
    intro X0
    first
    | (have i₁ := eq41773 X0
       have i₂ := eq41268
       grind)
    | exact superpose eq41268 eq41773
    | exact resolve eq41773 eq41268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41773
  have eq41883 : ∀ X0 : G, (M.op (M.op y y) y) ≠ (M.op (M.op (M.op y y) y) y) ∨ (M.op X0 (M.op y y)) = (k X0 (M.op (M.op (M.op y y) (M.op y y)) y)) := by
    intro X0
    first
    | (have i₁ := eq41763 X0
       have i₂ := eq41268
       grind)
    | exact superpose eq41268 eq41763
    | (have j0 := eq41763 X0
       grind)
    | exact resolve eq41763 eq41268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41763
  have eq41978 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = (M.op (σ (M.op y y)) X0) := by
    intro X0
    first
    | (have i₁ := eq41873 X0
       have i₂ := eq9 y y
       grind)
    | exact superpose eq9 eq41873
    | exact resolve eq41873 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41873
  have eq41988 : ∀ X0 : G, (M.op y y) ≠ (M.op (M.op y y) y) ∨ (M.op X0 (M.op y y)) = (k X0 (M.op (M.op (M.op y y) (M.op y y)) y)) := by
    intro X0
    first
    | (have i₁ := eq41883 X0
       have i₂ := eq9 y y
       grind)
    | exact superpose eq9 eq41883
    | (have j0 := eq41883 X0
       grind)
    | exact resolve eq41883 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41883
  have eq42044 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ (M.op y y)) X0) := by
    intro X0
    first
    | (have i₁ := eq41978 X0
       have i₂ := eq41582 X0
       grind)
    | exact superpose eq41582 eq41978
    | exact resolve eq41978 eq41582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41582 eq41978
  have eq42054 : ∀ X0 : G, (M.op X0 (M.op y y)) = (k X0 (M.op (M.op (M.op y y) (M.op y y)) y)) := by
    intro X0
    first
    | (have j0 := eq41988 X0
       grind)
    | (have r₁ := eq41988 X0
       have r₂ := eq41865 y
       grind)
    | exact resolve eq41988 eq41865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41988
  have eq42078 : ∀ X0 : G, (M.op X0 (M.op y y)) = (k X0 (M.op (M.op (M.op y y) y) y)) := by
    intro X0
    first
    | (have i₁ := eq42054 X0
       have i₂ := eq41268
       grind)
    | exact superpose eq41268 eq42054
    | exact resolve eq42054 eq41268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41268 eq42054
  have eq42091 : ∀ X0 : G, (k X0 (M.op y y)) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq42078 X0
       have i₂ := eq9 y y
       grind)
    | exact superpose eq9 eq42078
    | exact resolve eq42078 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42078
  have eq42097 : ∀ X0 : G, (k X0 (M.op y y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq42091 X0
       have i₂ := eq41600 X0
       grind)
    | exact superpose eq41600 eq42091
    | exact resolve eq42091 eq41600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42091
  have eq42148 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = (M.op (M.op y (M.op (M.op y y) y)) X0) := by
    intro X0
    first
    | (have i₁ := eq62 y X0
       have i₂ := eq41865 (M.op (M.op y y) y)
       grind)
    | exact superpose eq41865 eq62
    | exact resolve eq62 eq41865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq42163 : ∀ X0 : G, (σ (M.op y y)) ≠ (σ (M.op y (M.op y y))) ∨ (k X0 (σ (M.op y y))) = (M.op (σ (M.op y y)) X0) := by
    intro X0
    first
    | (have i₁ := eq359 (M.op y y) X0
       have i₂ := eq41865 (M.op y y)
       grind)
    | exact superpose eq41865 eq359
    | (have j0 := eq359 (M.op y y) X0
       grind)
    | exact resolve eq359 eq41865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq42346 : ∀ X0 : G, (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (k X0 (σ (M.op y y))) = (M.op (σ (M.op y y)) X0) := by
    intro X0
    first
    | (have i₁ := eq42163 X0
       have i₂ := eq41600 y
       grind)
    | exact superpose eq41600 eq42163
    | (have j0 := eq42163 X0
       grind)
    | exact resolve eq42163 eq41600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41600 eq42163
  have eq42347 : ∀ X0 : G, (k X0 (σ (M.op y y))) = (M.op (σ (M.op y y)) X0) := by
    intro X0
    first
    | (have j0 := eq42346 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42346
  have eq42359 : ∀ X0 : G, (M.op (M.op (M.op y y) y) X0) = (M.op X0 (M.op (M.op y y) y)) := by
    intro X0
    first
    | (have i₁ := eq42148 X0
       have i₂ := eq41604 y
       grind)
    | exact superpose eq41604 eq42148
    | exact resolve eq42148 eq41604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42148
  have eq42425 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq42347 X0
       have i₂ := eq42044 X0
       grind)
    | exact superpose eq42044 eq42347
    | exact resolve eq42347 eq42044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42044 eq42347
  have eq42437 : ∀ X0 : G, (M.op (M.op (M.op y y) y) X0) = (M.op (M.op y y) X0) := by
    intro X0
    first
    | (have i₁ := eq42359 X0
       have i₂ := eq41604 X0
       grind)
    | exact superpose eq41604 eq42359
    | exact resolve eq42359 eq41604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41604 eq42359
  have eq42485 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (M.op y y) y) X0) := by
    intro X0
    first
    | (have i₁ := eq42437 X0
       have i₂ := eq41865 X0
       grind)
    | exact superpose eq41865 eq42437
    | exact resolve eq42437 eq41865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41865 eq42437
  have eq42510 : ∀ X0 : G, (M.op y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq42485 X0
       have i₂ := eq9 X0 y
       grind)
    | exact superpose eq9 eq42485
    | exact resolve eq42485 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42485
  have eq43242 : ∀ X0 : G, (k X0 (σ (M.op y y))) = (σ (M.op (τ X0) y)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (M.op y y)
       have i₂ := eq42097 (τ X0)
       grind)
    | exact superpose eq42097 eq17
    | exact resolve eq17 eq42097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq42097
  have eq43263 : ∀ X0 : G, (σ (M.op y (τ X0))) = (k X0 (σ (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq43242 X0
       have i₂ := eq42510 (τ X0)
       grind)
    | exact superpose eq42510 eq43242
    | exact resolve eq43242 eq42510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43242
  have eq43293 : ∀ X0 : G, (σ (M.op y (τ X0))) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq43263 X0
       have i₂ := eq42425 X0
       grind)
    | exact superpose eq42425 eq43263
    | exact resolve eq43263 eq42425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42425 eq43263
  have eq43814 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq43293 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq43293
    | exact resolve eq43293 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43293
  have eq44248 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq43814 x
       grind)
    | exact superpose eq43814 eq16
    | exact resolve eq16 eq43814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43814
  have eq44486 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq44248
       have i₂ := eq42510 x
       grind)
    | exact superpose eq42510 eq44248
    | exact resolve eq44248 eq42510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42510 eq44248
  have eq44487 : False := by grind
  exact eq44487
