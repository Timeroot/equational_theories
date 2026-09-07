import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation436`: `x = x ◇ (y ◇ (y ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation436 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law436 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law436.models_iff G M).mp hM
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
  have eq341 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq370 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq341 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq341
    | (have j0 := eq341 X0 X1
       grind)
    | exact resolve eq341 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq750 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq751 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq750
  have eq4480 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq751
       grind)
    | exact superpose eq751 eq16
    | exact resolve eq16 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4481 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq751
       grind)
    | exact superpose eq751 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq751
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq751
       grind)
    | exact resolve eq13 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq4482 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4481
  have eq4483 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4482
  have eq4485 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4483
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq4483
    | exact resolve eq4483 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4483
  have eq7609 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq370 y x
       have i₂ := eq4485
       grind)
    | exact superpose eq4485 eq370
    | (have j0 := eq370 y x
       grind)
    | exact resolve eq370 eq4485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq7611 : (k x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq4485
       grind)
    | exact superpose eq4485 eq10
    | exact resolve eq10 eq4485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4485
  have eq7652 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq7609
  have eq7679 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq7611
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7611
    | exact resolve eq7611 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7611
  have eq7680 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7652
       have r₂ := eq4480
       grind)
    | exact resolve eq7652 eq4480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4480 eq7652
  have eq7683 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq7679
       have r₂ := eq13 x y
       grind)
    | exact resolve eq7679 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7679
  have eq8093 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq80 x y
       have i₂ := eq7683
       grind)
    | exact superpose eq7683 eq80
    | (have j0 := eq80 x y
       grind)
    | exact resolve eq80 eq7683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq7683
  have eq8096 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8093
  have eq8097 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8096
  have eq8279 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq8097
       grind)
    | exact superpose eq8097 eq16
    | exact resolve eq16 eq8097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8097
  have eq8508 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8279
       have i₂ := eq7680
       grind)
    | exact superpose eq7680 eq8279
    | exact resolve eq8279 eq7680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7680 eq8279
  have eq8509 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8508
  have eq8510 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq8509
  have eq8755 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8510
       grind)
    | exact superpose eq8510 eq10
    | exact resolve eq10 eq8510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8510
  have eq8829 : x = y ∨ x = y := by
    first
    | (have i₁ := eq8755
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8755
    | exact resolve eq8755 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8755
  have eq8830 : x = y := by grind
  clear eq8829
  have eq9011 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8830
       grind)
    | exact superpose eq8830 eq16
    | exact resolve eq16 eq8830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8830
  have eq9012 : False := by grind
  exact eq9012

/-- `Equation436`: `x = x ◇ (y ◇ (y ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation436 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law436 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law436.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq46 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq47 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
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
  have eq82 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
  have eq84 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq347 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq376 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq347 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq347
    | (have j0 := eq347 X0 X1
       grind)
    | exact resolve eq347 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq755 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq82
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq82
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq82
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq82
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq82 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq756 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq755
  have eq4481 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq756
       grind)
    | exact superpose eq756 eq16
    | exact resolve eq16 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4482 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq756
       grind)
    | exact superpose eq756 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq756
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq756
       grind)
    | exact resolve eq13 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq4483 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4482
  have eq4484 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4483
  have eq4486 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4484
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4484
    | exact resolve eq4484 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4484
  have eq7680 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq376 y x
       have i₂ := eq4486
       grind)
    | exact superpose eq4486 eq376
    | (have j0 := eq376 y x
       grind)
    | exact resolve eq376 eq4486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq7682 : (k y x) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq4486
       grind)
    | exact superpose eq4486 eq10
    | exact resolve eq10 eq4486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4486
  have eq7723 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq7680
  have eq7750 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq7682
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7682
    | exact resolve eq7682 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7682
  have eq7751 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7723
       have r₂ := eq4481
       grind)
    | exact resolve eq7723 eq4481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4481 eq7723
  have eq7754 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x (k y x)
       grind)
    | (have r₁ := eq7750
       have r₂ := eq13 y x
       grind)
    | exact resolve eq7750 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7750
  have eq8200 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq84 x y
       have i₂ := eq7754
       grind)
    | exact superpose eq7754 eq84
    | (have j0 := eq84 x y
       grind)
    | exact resolve eq84 eq7754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq7754
  have eq8203 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8200
  have eq8204 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8203
  have eq8380 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq8204
       grind)
    | exact superpose eq8204 eq16
    | exact resolve eq16 eq8204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8204
  have eq8603 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8380
       have i₂ := eq7751
       grind)
    | exact superpose eq7751 eq8380
    | exact resolve eq8380 eq7751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7751 eq8380
  have eq8604 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8603
  have eq8605 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq8604
  have eq8820 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8605
       grind)
    | exact superpose eq8605 eq10
    | exact resolve eq10 eq8605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8605
  have eq8894 : x = y ∨ x = y := by
    first
    | (have i₁ := eq8820
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8820
    | exact resolve eq8820 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8820
  have eq8895 : x = y := by grind
  clear eq8894
  have eq9063 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8895
       grind)
    | exact superpose eq8895 eq16
    | exact resolve eq16 eq8895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8895
  have eq9064 : False := by grind
  exact eq9064

/-- `Equation4364`: `x ◇ (y ◇ z) = y ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_x_pxy_Equation4364 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4364 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4364.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X1 (M.op X2 X0)) := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq77 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
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
  have eq83 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq77 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq87 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq83 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq83 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq83 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq128 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq87 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq129 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq128 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq133 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq129 (σ X0)
       grind)
    | exact superpose eq129 eq15
    | exact resolve eq15 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq133 X0
       have i₂ := eq129 X0
       grind)
    | exact superpose eq129 eq133
    | exact resolve eq133 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq133
  have eq252 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op (σ X0) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq144 X0
       grind)
    | exact superpose eq144 eq9
    | exact resolve eq9 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq144 X0
       grind)
    | exact superpose eq144 eq14
    | (have j0 := eq14 X1 X1
       grind)
    | exact resolve eq14 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq144 X0
       grind)
    | exact superpose eq144 eq14
    | (have j0 := eq14 X1 X1
       grind)
    | exact resolve eq14 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq144 X0
       grind)
    | exact superpose eq144 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq257 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq254 X0 X1
       have j1 := eq256 X0 X1
       grind)
    | (have r₁ := eq254 X0 X1
       have r₂ := eq256 X0 X1
       grind)
    | exact resolve eq254 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq258 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq253 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq253 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq253 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq1249 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq257 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq257
    | (have j0 := eq257 X0 X1
       grind)
    | exact resolve eq257 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq1489 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq1249 (τ X0) X1
       grind)
    | exact superpose eq1249 eq17
    | (have j1 := eq1249 X0 X1
       grind)
    | exact resolve eq17 eq1249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1249
  have eq12206 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1489 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1489
    | (have j0 := eq1489 X0 X1
       grind)
    | exact resolve eq1489 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489
  have eq12471 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12206 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq12206
    | (have j0 := eq12206 X0 X1
       grind)
    | exact resolve eq12206 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12206
  have eq29946 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq258 X0 X1
       grind)
    | exact superpose eq258 eq10
    | (have j1 := eq258 X0 X1
       grind)
    | exact resolve eq10 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq30026 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29946 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29946
    | (have j0 := eq29946 X0 X1
       grind)
    | exact resolve eq29946 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29946
  have eq33697 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq30026 X1 (σ X0)
       grind)
    | exact superpose eq30026 eq15
    | (have j1 := eq30026 X1 X1
       grind)
    | exact resolve eq15 eq30026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30026
  have eq47740 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33697 x y
       grind)
    | exact superpose eq33697 eq16
    | (have j1 := eq33697 x y
       grind)
    | exact resolve eq16 eq33697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33697
  have eq48107 : y = (M.op y y) := by
    first
    | (have j1 := eq12471 x y
       grind)
    | (have r₁ := eq47740
       have r₂ := eq12471 x y
       grind)
    | exact resolve eq47740 eq12471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12471 eq47740
  have eq53293 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq48107
       grind)
    | exact superpose eq48107 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq48107
       grind)
    | exact resolve eq12 eq48107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53295 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq256 y X0
       have i₂ := eq48107
       grind)
    | exact superpose eq48107 eq256
    | (have j0 := eq256 y X0
       grind)
    | exact resolve eq256 eq48107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq53300 : ∀ X0 : G, (M.op X0 y) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq48107
       grind)
    | exact superpose eq48107 eq9
    | exact resolve eq9 eq48107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53356 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq53295 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53295
  have eq53358 : ∀ X0 : G, (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq53293 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53293
  have eq62616 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq53356 (σ X0)
       grind)
    | exact superpose eq53356 eq15
    | exact resolve eq15 eq53356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53356
  have eq62648 : ∀ X0 : G, (σ (M.op y X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq62616 X0
       have i₂ := eq53358 X0
       grind)
    | exact superpose eq53358 eq62616
    | exact resolve eq62616 eq53358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53358 eq62616
  have eq74875 : ∀ X0 : G, (M.op (σ X0) (σ (M.op y y))) = (M.op (σ y) (σ (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq252 y (σ X0)
       have i₂ := eq62648 X0
       grind)
    | exact superpose eq62648 eq252
    | exact resolve eq252 eq62648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq74986 : ∀ X0 : G, (M.op (σ X0) (σ (M.op y y))) = (σ (M.op y (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq74875 X0
       have i₂ := eq62648 (M.op y X0)
       grind)
    | exact superpose eq62648 eq74875
    | exact resolve eq74875 eq62648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62648 eq74875
  have eq75004 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) (σ (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq74986 X0
       have i₂ := eq53300 X0
       grind)
    | exact superpose eq53300 eq74986
    | exact resolve eq74986 eq53300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53300 eq74986
  have eq75007 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq75004 X0
       have i₂ := eq48107
       grind)
    | exact superpose eq48107 eq75004
    | exact resolve eq75004 eq48107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48107 eq75004
  have eq82149 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq75007 x
       grind)
    | exact superpose eq75007 eq16
    | (have r₁ := eq16
       have r₂ := eq75007 x
       grind)
    | exact resolve eq16 eq75007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75007
  have eq82247 : False := by grind
  exact eq82247

/-- `Equation4369`: `x ◇ (y ◇ z) = z ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_x_pxy_Equation4369 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4369 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4369.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X2 (M.op X1 X0)) := by
    intro X0 X1 X2
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
  have eq74 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq75 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq81 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq75 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq82 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq74 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq85 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq81 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq81 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq81 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq86 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq82 X0 X1 X1
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq82 X0 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq82 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq82 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq126 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq85 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq127 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq126 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq131 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq127 (σ X0)
       grind)
    | exact superpose eq127 eq15
    | exact resolve eq15 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq131 X0
       have i₂ := eq127 X0
       grind)
    | exact superpose eq127 eq131
    | exact resolve eq131 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq221 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op (σ X0) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq142 X0
       grind)
    | exact superpose eq142 eq9
    | exact resolve eq9 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq142 X0
       grind)
    | exact superpose eq142 eq14
    | (have j0 := eq14 X1 X1
       grind)
    | exact resolve eq14 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq142 X0
       grind)
    | exact superpose eq142 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq227 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq222 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq222 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq222 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq389 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq127 X0
       have i₂ := eq86 X0 X0 X1
       grind)
    | exact superpose eq86 eq127
    | (have j1 := eq86 X0 X0 X1
       grind)
    | exact resolve eq127 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq127
  have eq409 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq389 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq456 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq409 X1 (τ X0)
       grind)
    | exact superpose eq409 eq17
    | (have j1 := eq409 X1 X1
       grind)
    | exact resolve eq17 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq409
  have eq3379 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq456 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq456
    | (have j0 := eq456 X0 X1
       grind)
    | exact resolve eq456 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq3523 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3379 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3379
    | (have j0 := eq3379 X0 X1
       grind)
    | exact resolve eq3379 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3379
  have eq6202 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq227 X0 X1
       grind)
    | exact superpose eq227 eq10
    | (have j1 := eq227 X0 X1
       grind)
    | exact resolve eq10 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq6278 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6202 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6202
    | (have j0 := eq6202 X0 X1
       grind)
    | exact resolve eq6202 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6202
  have eq7019 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq6278 X1 (σ X0)
       grind)
    | exact superpose eq6278 eq15
    | (have j1 := eq6278 X1 X1
       grind)
    | exact resolve eq15 eq6278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6278
  have eq9874 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7019 x y
       grind)
    | exact superpose eq7019 eq16
    | (have j1 := eq7019 x y
       grind)
    | exact resolve eq16 eq7019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7019
  have eq10100 : y = (M.op y y) := by
    first
    | (have j1 := eq3523 x y
       grind)
    | (have r₁ := eq9874
       have r₂ := eq3523 x y
       grind)
    | exact resolve eq9874 eq3523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3523 eq9874
  have eq10505 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq10100
       grind)
    | exact superpose eq10100 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq10100
       grind)
    | exact resolve eq12 eq10100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10507 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq225 y X0
       have i₂ := eq10100
       grind)
    | exact superpose eq10100 eq225
    | (have j0 := eq225 y X0
       grind)
    | exact resolve eq225 eq10100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq10510 : ∀ X0 : G, (M.op X0 y) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq9 y y X0
       have i₂ := eq10100
       grind)
    | exact superpose eq10100 eq9
    | exact resolve eq9 eq10100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10557 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq10507 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10507
  have eq10559 : ∀ X0 : G, (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq10505 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10505
  have eq11845 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq10557 (σ X0)
       grind)
    | exact superpose eq10557 eq15
    | exact resolve eq15 eq10557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10557
  have eq11881 : ∀ X0 : G, (σ (M.op y X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11845 X0
       have i₂ := eq10559 X0
       grind)
    | exact superpose eq10559 eq11845
    | exact resolve eq11845 eq10559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10559 eq11845
  have eq14616 : ∀ X0 : G, (M.op (σ X0) (σ (M.op y y))) = (M.op (σ y) (σ (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq221 y (σ X0)
       have i₂ := eq11881 X0
       grind)
    | exact superpose eq11881 eq221
    | exact resolve eq221 eq11881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq14712 : ∀ X0 : G, (σ (M.op y (M.op y X0))) = (M.op (σ X0) (σ (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq14616 X0
       have i₂ := eq11881 (M.op y X0)
       grind)
    | exact superpose eq11881 eq14616
    | exact resolve eq14616 eq11881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11881 eq14616
  have eq14734 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op y (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq14712 X0
       have i₂ := eq10100
       grind)
    | exact superpose eq10100 eq14712
    | exact resolve eq14712 eq10100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10100 eq14712
  have eq14738 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14734 X0
       have i₂ := eq10510 X0
       grind)
    | exact superpose eq10510 eq14734
    | exact resolve eq14734 eq10510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10510 eq14734
  have eq16704 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14738 x
       grind)
    | exact superpose eq14738 eq16
    | (have r₁ := eq16
       have r₂ := eq14738 x
       grind)
    | exact resolve eq16 eq14738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14738
  have eq16793 : False := by grind
  exact eq16793

/-- `Equation4396`: `x ◇ (x ◇ y) = (x ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_x_pyx_Equation4396 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4396 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4396.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq79 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq94 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq117 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq94 X1 (τ X0)
       grind)
    | exact superpose eq94 eq20
    | (have j1 := eq94 X1 (τ X0)
       grind)
    | exact resolve eq20 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq119 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq94 (σ X1) (σ X0)
       grind)
    | exact superpose eq94 eq15
    | (have j1 := eq94 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  clear eq94
  have eq147 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq126 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq148 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq147 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq183 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq148 (σ X0)
       grind)
    | exact superpose eq148 eq15
    | exact resolve eq15 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq183 X0
       have i₂ := eq148 X0
       grind)
    | exact superpose eq148 eq183
    | exact resolve eq183 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq183
  have eq295 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq190 X0
       grind)
    | exact superpose eq190 eq9
    | exact resolve eq9 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq307 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq298 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq298
    | exact resolve eq298 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq312 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq307
  have eq1620 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq295 X0 (σ X0)
       have i₂ := eq190 X0
       grind)
    | exact superpose eq190 eq295
    | exact resolve eq295 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq1683 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1620 X0
       have i₂ := eq312 X0
       grind)
    | exact superpose eq312 eq1620
    | exact resolve eq1620 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312 eq1620
  have eq4525 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq117 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq117
    | exact resolve eq117 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq4688 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4525 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4525
    | (have j0 := eq4525 X0 X1
       grind)
    | exact resolve eq4525 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4525
  have eq6469 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq119 X1 X0
       grind)
    | exact superpose eq119 eq10
    | (have j1 := eq119 X1 X0
       grind)
    | exact resolve eq10 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq6628 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6469 X0 X1
       have i₂ := eq190 X0
       grind)
    | exact superpose eq190 eq6469
    | (have j0 := eq6469 X0 X1
       grind)
    | exact resolve eq6469 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq6469
  have eq6766 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6628 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq6628
    | (have j0 := eq6628 X0 X1
       grind)
    | exact resolve eq6628 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6628
  have eq7181 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6766 y x
       grind)
    | exact superpose eq6766 eq16
    | (have j1 := eq6766 y x
       grind)
    | exact resolve eq16 eq6766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6766
  have eq7277 : x = (M.op y y) := by
    first
    | (have j1 := eq4688 x y
       grind)
    | (have r₁ := eq7181
       have r₂ := eq4688 x y
       grind)
    | exact resolve eq7181 eq4688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4688 eq7181
  have eq7889 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq9 y X0
       have i₂ := eq7277
       grind)
    | exact superpose eq7277 eq9
    | exact resolve eq9 eq7277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7913 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq1683 y
       have i₂ := eq7277
       grind)
    | exact superpose eq7277 eq1683
    | exact resolve eq1683 eq7277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1683
  have eq8204 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq7889 y
       have i₂ := eq7277
       grind)
    | exact superpose eq7277 eq7889
    | exact resolve eq7889 eq7277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7277 eq7889
  have eq10501 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7913
       grind)
    | exact superpose eq7913 eq16
    | exact resolve eq16 eq7913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7913
  have eq10522 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq10501
       have i₂ := eq8204
       grind)
    | exact superpose eq8204 eq10501
    | exact resolve eq10501 eq8204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8204 eq10501
  have eq10523 : False := by grind
  exact eq10523

/-- `Equation4400`: `x ◇ (x ◇ y) = (x ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_y_x_pxx_pyx_Equation4400 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4400 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4400.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X2) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X1 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq42 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq956 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) X2) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) (σ X0) X2
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq9
    | (have j1 := eq42 X0 X1
       grind)
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq970 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq42 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq971 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq970 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq45460 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq956 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq45497 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq45460 X0 X1
       have j1 := eq42 X0 X1
       grind)
    | (have r₁ := eq45460 X0 X0
       have r₂ := eq42 X0 X1
       grind)
    | (have r₁ := eq45460 X0 X1
       have r₂ := eq42 X0 X1
       grind)
    | exact resolve eq45460 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq45460
  have eq57660 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq45497 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45497
    | exact resolve eq45497 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45497
  have eq58005 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq57660 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq57660
    | (have j0 := eq57660 X0 X1
       grind)
    | exact resolve eq57660 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq57660
  have eq59236 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq58005 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq58005
    | (have j0 := eq58005 X1 X1
       grind)
    | exact resolve eq58005 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58005
  have eq60574 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq59236 (τ X1) X0
       grind)
    | exact superpose eq59236 eq17
    | (have j1 := eq59236 X0 X0
       grind)
    | exact resolve eq17 eq59236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq60595 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq59236 X1 X0
       grind)
    | exact superpose eq59236 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq59236 X1 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq59236 X0 X1
       grind)
    | exact resolve eq12 eq59236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60916 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq60595 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60595
  have eq62182 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X0)
       have i₂ := eq60916 (σ X0) X1
       grind)
    | exact superpose eq60916 eq37
    | (have j1 := eq60916 (σ X0) X1
       grind)
    | exact resolve eq37 eq60916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq60916
  have eq62345 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq62182 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq62182
    | (have j0 := eq62182 X0 X1
       grind)
    | exact resolve eq62182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62182
  have eq72304 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq62345 X0 (σ X1)
       grind)
    | exact superpose eq62345 eq15
    | (have j1 := eq62345 X0 X1
       grind)
    | exact resolve eq15 eq62345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62345
  have eq81039 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60574 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq60574
    | (have j0 := eq60574 X1 X1
       grind)
    | exact resolve eq60574 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60574
  have eq81820 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81039 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq81039
    | (have j0 := eq81039 X0 X1
       grind)
    | exact resolve eq81039 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81039
  have eq82818 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq81820 X1 X0
       grind)
    | exact superpose eq81820 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq81820 X1 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq81820 X0 X1
       grind)
    | exact resolve eq12 eq81820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81820
  have eq83155 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq82818 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82818
  have eq96654 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq72304 x y
       grind)
    | exact superpose eq72304 eq16
    | (have j1 := eq72304 x x
       grind)
    | exact resolve eq16 eq72304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72304
  have eq97094 : x = (k x x) := by
    first
    | (have j1 := eq83155 x x
       grind)
    | (have r₁ := eq96654
       have r₂ := eq83155 x y
       grind)
    | exact resolve eq96654 eq83155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83155 eq96654
  have eq98676 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq971 x
       have i₂ := eq97094
       grind)
    | exact superpose eq97094 eq971
    | (have j0 := eq971 x
       grind)
    | exact resolve eq971 eq97094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971
  have eq98706 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq59236 x x
       have i₂ := eq97094
       grind)
    | exact superpose eq97094 eq59236
    | (have j0 := eq59236 x x
       grind)
    | exact resolve eq59236 eq97094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59236 eq97094
  have eq98710 : x = (M.op x x) := by grind
  clear eq98706
  have eq98733 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq98676
  have eq100711 : ∀ X0 X1 : G, (M.op x X1) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 x x x x
       have i₂ := eq98710
       grind)
    | exact superpose eq98710 eq19
    | exact resolve eq19 eq98710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101411 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq98710
       have i₂ := eq100711 X0 x
       grind)
    | (have i₁ := eq98710
       have i₂ := eq100711 x X0
       grind)
    | exact superpose eq100711 eq98710
    | exact resolve eq98710 eq100711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98710 eq100711
  have eq108765 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ x) (σ x) x x
       have i₂ := eq98733
       grind)
    | exact superpose eq98733 eq19
    | exact resolve eq19 eq98733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq118194 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq108765 (σ y) X0
       grind)
    | (have i₁ := eq16
       have i₂ := eq108765 X0 (σ y)
       grind)
    | exact superpose eq108765 eq16
    | exact resolve eq16 eq108765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118195 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq98733
       have i₂ := eq108765 (σ x) X0
       grind)
    | (have i₁ := eq98733
       have i₂ := eq108765 X0 (σ x)
       grind)
    | exact superpose eq108765 eq98733
    | exact resolve eq98733 eq108765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98733 eq108765
  have eq118448 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq118194 x
       have i₂ := eq118195 x
       grind)
    | exact superpose eq118195 eq118194
    | exact resolve eq118194 eq118195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118194 eq118195
  have eq118496 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq118448
       have i₂ := eq101411 y
       grind)
    | exact superpose eq101411 eq118448
    | exact resolve eq118448 eq101411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101411 eq118448
  have eq118497 : False := by grind
  exact eq118497

/-- `Equation4408`: `x ◇ (x ◇ y) = (y ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_x_pxy_Equation4408 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4408 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4408.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq534 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq541 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq534 X0 X1
       have j1 := eq67 X0 X1
       grind)
    | (have r₁ := eq534 X0 X0
       have r₂ := eq67 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq534 X0 X1
       have r₂ := eq67 X0 X1
       grind)
    | (have r₁ := eq534 X1 X0
       have r₂ := eq67 X0 X1
       grind)
    | exact resolve eq534 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq534
  have eq576 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq1023 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq576 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq1024 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1023 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq1181 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1024 (σ X0)
       grind)
    | exact superpose eq1024 eq15
    | exact resolve eq15 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1192 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1181 X0
       have i₂ := eq1024 X0
       grind)
    | exact superpose eq1024 eq1181
    | exact resolve eq1181 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024 eq1181
  have eq1868 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq1885 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq541 (σ X0) X1
       have i₂ := eq1192 X0
       grind)
    | exact superpose eq1192 eq541
    | (have j0 := eq541 (σ X0) X1
       grind)
    | exact resolve eq541 eq1192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192
  have eq1891 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1868 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq1868
    | exact resolve eq1868 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1868
  have eq1899 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq1891
  have eq5462 : ∀ X0 X1 : G, (M.op X1 X1) = (τ X0) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq1885 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq1885 X0 (σ X0)
       grind)
    | exact superpose eq1885 eq10
    | (have j1 := eq1885 X1 X0
       grind)
    | exact resolve eq10 eq1885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885
  have eq7727 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq5462 (σ X1) X0
       grind)
    | exact superpose eq5462 eq15
    | (have j1 := eq5462 (σ X1) X0
       grind)
    | exact resolve eq15 eq5462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5462
  have eq7768 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7727 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq7727
    | (have j0 := eq7727 X0 X1
       grind)
    | exact resolve eq7727 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7727
  have eq10577 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7768 x y
       grind)
    | exact superpose eq7768 eq16
    | (have j1 := eq7768 x y
       grind)
    | exact resolve eq16 eq7768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7768
  have eq11281 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10577
       have i₂ := eq541 x y
       grind)
    | exact superpose eq541 eq10577
    | (have j1 := eq541 x y
       grind)
    | exact resolve eq10577 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541 eq10577
  have eq11287 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq11281
  have eq11288 : y = (M.op x x) := by grind
  clear eq11287
  have eq11464 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1899 x
       have i₂ := eq11288
       grind)
    | exact superpose eq11288 eq1899
    | exact resolve eq1899 eq11288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1899 eq11288
  have eq11493 : False := by grind
  exact eq11493

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation442 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq42 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq149 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
  have eq156 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq634 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq42
    | exact resolve eq42 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq679 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq634 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq634
    | (have j0 := eq634 X0 X1
       grind)
    | exact resolve eq634 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq1048 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq149
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq149
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq149
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq149
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq149 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq1049 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1048
  have eq15619 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1049
       grind)
    | exact superpose eq1049 eq16
    | exact resolve eq16 eq1049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15627 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq1049
       grind)
    | exact superpose eq1049 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1049
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1049
       grind)
    | exact resolve eq13 eq1049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq15674 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq15627
  have eq15675 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq15674
  have eq15694 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq15675
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq15675
    | exact resolve eq15675 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15675
  have eq28409 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq679 x y
       have i₂ := eq15694
       grind)
    | exact superpose eq15694 eq679
    | (have j0 := eq679 x y
       grind)
    | exact resolve eq679 eq15694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq28410 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq15694
       grind)
    | exact superpose eq15694 eq10
    | exact resolve eq10 eq15694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15694
  have eq28481 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq28409
  have eq28523 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq28410
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq28410
    | exact resolve eq28410 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28410
  have eq28524 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq28481
       have r₂ := eq15619
       grind)
    | exact resolve eq28481 eq15619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15619 eq28481
  have eq28527 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq28523
       have r₂ := eq13 x y
       grind)
    | exact resolve eq28523 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28523
  have eq29073 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq156 x y
       have i₂ := eq28527
       grind)
    | exact superpose eq28527 eq156
    | (have j0 := eq156 x y
       grind)
    | exact resolve eq156 eq28527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq28527
  have eq29093 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq29073
  have eq29094 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq29093
  have eq30506 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq29094
       grind)
    | exact superpose eq29094 eq16
    | exact resolve eq16 eq29094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29094
  have eq30891 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq30506
       have i₂ := eq28524
       grind)
    | exact superpose eq28524 eq30506
    | exact resolve eq30506 eq28524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28524 eq30506
  have eq30892 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq30891
  have eq30893 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq30892
  have eq31119 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq30893
       grind)
    | exact superpose eq30893 eq10
    | exact resolve eq10 eq30893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30893
  have eq31227 : x = y ∨ x = y := by
    first
    | (have i₁ := eq31119
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq31119
    | exact resolve eq31119 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31119
  have eq31228 : x = y := by grind
  clear eq31227
  have eq31453 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31228
       grind)
    | exact superpose eq31228 eq16
    | exact resolve eq16 eq31228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31228
  have eq31454 : False := by grind
  exact eq31454
