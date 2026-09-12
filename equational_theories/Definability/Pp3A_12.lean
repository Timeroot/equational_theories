import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pyx_x_pyx_Equation2666 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X0 := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq42 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq35 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, x = (M.op (M.op (M.op x X0) (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X3 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq63 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq65 : y ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
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
  have eq77 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq78 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq85 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq16
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq85
    | (have j0 := eq85 (σ X0) (σ X1)
       grind)
    | exact resolve eq85 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq85 x x
       grind)
    | exact superpose eq85 eq43
    | (have j1 := eq85 x x
       grind)
    | exact resolve eq43 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq77
       have i₂ := eq85 y x
       grind)
    | exact superpose eq85 eq77
    | (have j1 := eq85 y x
       grind)
    | exact resolve eq77 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq85 y y
       grind)
    | exact superpose eq85 eq78
    | (have j1 := eq85 y y
       grind)
    | exact resolve eq78 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104
    | exact resolve eq104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq116
    | exact resolve eq116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq270 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op (τ X0) x)) ∨ (τ X0) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq85 x (τ X0)
       grind)
    | exact superpose eq85 eq42
    | (have j1 := eq85 x (τ X0)
       grind)
    | exact resolve eq42 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq564 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq117 eq85
    | (have j0 := eq85 (σ y) (σ x)
       grind)
    | exact resolve eq85 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq565 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq564
    | exact resolve eq564 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq568 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq565
       have r₂ := eq27
       grind)
    | exact resolve eq565 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq609 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (σ (k X0 X1)) (M.op (σ X1) X2)) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X1) (σ X0) X2
       have i₂ := eq97 X0 X1
       grind)
    | exact superpose eq97 eq14
    | (have j1 := eq97 X0 X1
       grind)
    | exact resolve eq14 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq628 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq568 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq568
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq568
       grind)
    | exact resolve eq13 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq631 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq628
  have eq635 : (τ (σ x)) = (k x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq631 eq59
    | exact resolve eq59 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq637 : x = (k x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq635
    | exact resolve eq635 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq640 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq85 x y
       have i₂ := eq637
       grind)
    | exact superpose eq637 eq85
    | (have j0 := eq85 y x
       grind)
    | exact resolve eq85 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq641 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq640
  have eq643 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq641
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq641
    | exact resolve eq641 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq648 : ∀ X0 : G, y = (M.op (M.op (M.op y X0) x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq643
       grind)
    | exact superpose eq643 eq14
    | exact resolve eq14 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op x X0) (M.op x y)) X1)) = (M.op (M.op (M.op (M.op x X0) (M.op x y)) (M.op (M.op x (M.op (M.op (M.op x X0) (M.op x y)) X1)) X2)) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq667 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq681 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X1 X2 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X2)) (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X2)) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X2)) X3) X1
       have i₂ := eq52 X0 (M.op X0 X1) X2 X3
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq683 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x (M.op x y)) (M.op x X0)) (M.op (M.op (M.op x (M.op x y)) (M.op x X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op (M.op x sF0) (M.op x x)) x)
       have i₂ := eq52 x sF0 x x
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq738 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) X5)) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3 X2 X3
       have i₂ := eq55 X0 X1 X2 X3
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq759 : y = (M.op (M.op x x) x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq648 x
       have i₂ := eq643
       grind)
    | exact superpose eq643 eq648
    | exact resolve eq648 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643 eq648
  have eq769 : y = (M.op (M.op x x) x) ∨ y = (M.op x y) := by grind
  clear eq759
  have eq906 : ∀ X0 : G, (M.op y (M.op (M.op x x) X0)) = (M.op (M.op (M.op x x) (M.op x x)) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq681 (M.op x x) x X0
       have i₂ := eq769
       grind)
    | exact superpose eq769 eq681
    | exact resolve eq681 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq916 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq681
    | (have j0 := eq681 (σ x) (σ y) X0
       grind)
    | exact resolve eq681 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq938 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq681
    | (have j0 := eq681 (σ x) X0 (σ y)
       grind)
    | exact resolve eq681 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq945 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq681 X0 X1 x
       grind)
    | exact superpose eq681 eq14
    | exact resolve eq14 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq985 : ∀ X0 : G, x = (M.op y (M.op (M.op x x) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq906 X0
       have i₂ := eq14 x x x
       grind)
    | exact superpose eq14 eq906
    | exact resolve eq906 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq1036 : x = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq985 x
       have i₂ := eq769
       grind)
    | exact superpose eq769 eq985
    | exact resolve eq985 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769 eq985
  have eq1053 : x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq1036
  have eq1058 : x ≠ y ∨ x = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1053
       grind)
    | exact superpose eq1053 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq1053
       grind)
    | exact resolve eq13 eq1053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1066 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq681 y y x
       have i₂ := eq1053
       grind)
    | exact superpose eq1053 eq681
    | exact resolve eq681 eq1053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1072 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1066 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1066
    | (have j0 := eq1066 X0
       grind)
    | exact resolve eq1066 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066
  have eq1139 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1072 y
       have i₂ := eq1053
       grind)
    | exact superpose eq1053 eq1072
    | exact resolve eq1072 eq1053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1155 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq1139
  have eq1177 : x ≠ (M.op x y) ∨ (M.op x y) = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq1155
       grind)
    | exact superpose eq1155 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq1155
       grind)
    | exact resolve eq13 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5989 : ∀ X1 : G, x = (M.op (M.op (M.op x x) (M.op x y)) (M.op (M.op (M.op x x) (M.op x y)) X1)) := by
    intro X1
    first
    | (have i₁ := eq683 x X1
       have i₂ := eq681 x sF0 x
       grind)
    | exact superpose eq681 eq683
    | exact resolve eq683 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq7605 : ∀ X0 : G, (σ x) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq609 x x X0
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq609
    | (have j0 := eq609 x x x
       grind)
    | exact resolve eq609 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq7728 : ∀ X0 : G, (σ x) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq7605 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7605
    | (have j0 := eq7605 X0
       grind)
    | exact resolve eq7605 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7605
  have eq7795 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq7728 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7728
    | (have j0 := eq7728 X0
       grind)
    | exact resolve eq7728 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7728
  have eq8007 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X1)) (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X3)) = X0 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq682 X0 X1 x X3
       have i₂ := eq681 X0 (M.op X0 X1) x
       grind)
    | exact superpose eq681 eq682
    | exact resolve eq682 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq8008 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X0) X3)) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq8007 x x X3
       have i₂ := eq681 x x x
       grind)
    | exact superpose eq681 eq8007
    | exact resolve eq8007 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8007
  have eq8180 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq681 (M.op (M.op X0 X0) X0) X1 (M.op (M.op (M.op X0 X0) X0) x)
       have i₂ := eq8008 X0 x
       grind)
    | exact superpose eq8008 eq681
    | exact resolve eq681 eq8008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8008
  have eq8181 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8180 X0 X1
       have i₂ := eq681 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq681 eq8180
    | exact resolve eq8180 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8180
  have eq8187 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8181 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq8181
    | exact resolve eq8181 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8181
  have eq9858 : ∀ X1 : G, (M.op x x) = (M.op (M.op (M.op (M.op x x) (M.op x y)) (M.op (M.op x x) X1)) x) := by
    intro X1
    first
    | exact superpose eq5989 eq659
    | exact resolve eq659 eq5989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659 eq5989
  have eq9884 : (M.op x x) = (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op x y)) x) := by
    first
    | (have i₁ := eq9858 x
       have i₂ := eq681 (M.op x x) sF0 x
       grind)
    | exact superpose eq681 eq9858
    | exact resolve eq9858 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9858
  have eq9893 : (M.op x x) = (M.op (M.op (M.op (M.op x x) x) (M.op x y)) x) := by
    first
    | (have i₁ := eq9884
       have i₂ := eq681 x x x
       grind)
    | exact superpose eq681 eq9884
    | exact resolve eq9884 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9884
  have eq13680 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) X3) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq667 X0 X1 x X3 X4
       have i₂ := eq681 X0 X1 x
       grind)
    | exact superpose eq681 eq667
    | exact resolve eq667 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq13723 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13680 X1 (M.op X1 X2) X1 x
       have i₂ := eq14 X1 X1 X2
       grind)
    | exact superpose eq14 eq13680
    | exact resolve eq13680 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13757 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13680 (M.op X0 X2) (M.op X0 X2) X0 x
       have i₂ := eq55 X0 X2 X2 (M.op X0 X2)
       grind)
    | exact superpose eq55 eq13680
    | exact resolve eq13680 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13760 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X2)) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13680 X1 X1 (M.op (M.op X1 X1) X2) x
       have i₂ := eq14 (M.op X1 X1) X1 X2
       grind)
    | exact superpose eq14 eq13680
    | exact resolve eq13680 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13776 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X0) X0) (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X0) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X0 X0 X1 (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X0) X0) X2)
       have i₂ := eq13680 X0 (M.op X0 X1) X0 X2
       grind)
    | exact superpose eq13680 eq55
    | exact resolve eq55 eq13680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq13680
  have eq13820 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13776 X1 X2 X2
       have i₂ := eq14 X1 X1 X2
       grind)
    | exact superpose eq14 eq13776
    | exact resolve eq13776 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13776
  have eq13834 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13760 X0 X1 x
       have i₂ := eq681 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq681 eq13760
    | exact resolve eq13760 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13760
  have eq13835 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13757 X0 X1 x
       have i₂ := eq681 (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1) x
       grind)
    | exact superpose eq681 eq13757
    | exact resolve eq13757 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13757
  have eq13866 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13723 X0 X1 x
       have i₂ := eq681 (M.op X0 X0) (M.op X0 X1) x
       grind)
    | exact superpose eq681 eq13723
    | exact resolve eq13723 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13723
  have eq13882 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq13820 X0 x X2
       have i₂ := eq681 X0 X0 x
       grind)
    | exact superpose eq681 eq13820
    | exact resolve eq13820 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13820
  have eq13896 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13834 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq13834
    | exact resolve eq13834 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13834
  have eq13897 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13835 X0 X1
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq13835
    | exact resolve eq13835 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13835
  have eq13927 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13866 X0 X1
       have i₂ := eq681 X0 X0 X0
       grind)
    | exact superpose eq681 eq13866
    | exact resolve eq13866 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13866
  have eq13947 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13897 X0 X1
       have i₂ := eq681 X0 X1 X1
       grind)
    | exact superpose eq681 eq13897
    | exact resolve eq13897 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13897
  have eq19980 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) X5)) X3) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq738 X0 X1 x X3 X4 X5
       have i₂ := eq681 X0 X1 x
       grind)
    | exact superpose eq681 eq738
    | exact resolve eq738 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq20135 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X2)) = (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X2)) X3)) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19980 X1 X1 (M.op (M.op X1 X1) X2) x x
       have i₂ := eq14 (M.op X1 X1) X1 X2
       grind)
    | exact superpose eq14 eq19980
    | exact resolve eq19980 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19980
  have eq20221 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X2)) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X2)) X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq20135 X0 x X2 X3
       have i₂ := eq681 (M.op X0 X0) (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X2)) X3) x
       grind)
    | exact superpose eq681 eq20135
    | exact resolve eq20135 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20135
  have eq20310 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq20221 x x X3
       have i₂ := eq681 (M.op x x) x x
       grind)
    | exact superpose eq681 eq20221
    | exact resolve eq20221 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20221
  have eq20381 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X3)) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq20310 x X3
       have i₂ := eq14 x x x
       grind)
    | exact superpose eq14 eq20310
    | exact resolve eq20310 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20310
  have eq20428 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X3)) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq20381 X0 X3
       have i₂ := eq681 X0 X0 X0
       grind)
    | exact superpose eq681 eq20381
    | exact resolve eq20381 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681 eq20381
  have eq41224 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq1155
       grind)
    | exact superpose eq1155 eq103
    | exact resolve eq103 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq1155
  have eq41285 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq41224
    | exact resolve eq41224 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41224
  have eq41290 : (τ (σ (M.op x y))) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41285 eq49
    | exact resolve eq49 eq41285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq41285
  have eq41302 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq41290
    | exact resolve eq41290 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq41290
  have eq41305 : (M.op x y) = (k x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq41302
       have r₂ := eq1177
       grind)
    | exact resolve eq41302 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177 eq41302
  have eq41307 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43
       have i₂ := eq41305
       grind)
    | exact superpose eq41305 eq43
    | exact resolve eq43 eq41305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq41305
  have eq41337 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq41307
    | exact resolve eq41307 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41307
  have eq41353 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq41337
       have i₂ := eq85 sF2 sF2
       grind)
    | exact superpose eq85 eq41337
    | (have j1 := eq85 (σ x) (σ x)
       grind)
    | exact resolve eq41337 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41373 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq106
       have i₂ := eq1053
       grind)
    | exact superpose eq1053 eq106
    | exact resolve eq106 eq1053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq1053
  have eq41432 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41373
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq41373
    | exact resolve eq41373 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41373
  have eq41437 : (τ (σ x)) = (k y y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq41432 eq90
    | exact resolve eq90 eq41432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq41432
  have eq41449 : x = (k y y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq41437
    | exact resolve eq41437 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41437
  have eq41452 : x = (k y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq41449
       have r₂ := eq1058
       grind)
    | exact resolve eq41449 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058 eq41449
  have eq41454 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq41452
       grind)
    | exact superpose eq41452 eq78
    | exact resolve eq78 eq41452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq41452
  have eq41484 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41454
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq41454
    | exact resolve eq41454 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41454
  have eq41500 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq41484
       have i₂ := eq85 sF3 sF3
       grind)
    | exact superpose eq85 eq41484
    | (have j1 := eq85 (σ y) (σ y)
       grind)
    | exact resolve eq41484 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42583 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq41500 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq41500
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq41500
       grind)
    | exact resolve eq13 eq41500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42595 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq41500
  have eq42596 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq42583
  have eq43208 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq42596 eq41484
    | exact resolve eq41484 eq42596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41484 eq42596
  have eq43221 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq43208
  have eq43235 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq43221
       have r₂ := eq42595
       grind)
    | exact resolve eq43221 eq42595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42595 eq43221
  have eq43270 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq43235 eq945
    | exact resolve eq945 eq43235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43235
  have eq43442 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43270 eq13896
    | exact resolve eq13896 eq43270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43270
  have eq43507 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq43442
    | exact resolve eq43442 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43442
  have eq43749 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43507 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq43507
       grind)
    | exact resolve eq13 eq43507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50504 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq9893
       have i₂ := eq8187 x sF0
       grind)
    | exact superpose eq8187 eq9893
    | exact resolve eq9893 eq8187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9893
  have eq68462 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43507 eq41353
    | exact resolve eq41353 eq43507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41353 eq43507
  have eq68652 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq68462
  have eq68680 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq68652
       have r₂ := eq27
       grind)
    | exact resolve eq68652 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68652
  have eq68686 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq68680 eq27
    | exact resolve eq27 eq68680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68806 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq68680 eq43749
    | (have r₁ := eq43749
       have r₂ := eq68680
       grind)
    | exact resolve eq43749 eq68680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43749 eq68680
  have eq69016 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq68806
  have eq69017 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq69016
  have eq70840 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq69017 eq41337
    | exact resolve eq41337 eq69017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41337 eq69017
  have eq70854 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq70840
  have eq70868 : y = (M.op x y) := by
    first
    | (have r₁ := eq70854
       have r₂ := eq68686
       grind)
    | exact resolve eq70854 eq68686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68686 eq70854
  have eq70985 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq70868 eq20
    | exact resolve eq20 eq70868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq70990 : y ≠ y ∨ y = (k y x) := by
    first
    | exact superpose eq70868 eq65
    | (have r₁ := eq65
       have r₂ := eq70868
       grind)
    | exact resolve eq65 eq70868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq71076 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq70868 eq50504
    | exact resolve eq50504 eq70868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50504
  have eq71079 : y = (k y x) := by grind
  clear eq70990
  have eq71080 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq71076
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq71076
    | exact resolve eq71076 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq71076
  have eq71144 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq70985
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq70985
    | exact resolve eq70985 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70985
  have eq71145 : y = (M.op x x) := by
    first
    | exact superpose eq70868 eq71080
    | exact resolve eq71080 eq70868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71080
  have eq71148 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq71144 eq26
    | exact resolve eq26 eq71144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq71625 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq71079
       grind)
    | exact superpose eq71079 eq77
    | exact resolve eq77 eq71079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq71079
  have eq71663 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq71144 eq71625
    | exact resolve eq71625 eq71144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71625
  have eq71682 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq71663
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq71663
    | exact resolve eq71663 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71663
  have eq71699 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq71144 eq71682
    | exact resolve eq71682 eq71144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71682
  have eq72079 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq71699 eq85
    | (have j0 := eq85 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq85 eq71699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq71699
  have eq72093 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq71148 eq72079
    | exact resolve eq72079 eq71148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72079
  have eq72098 : (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq72093
       have r₂ := eq27
       grind)
    | exact resolve eq72093 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72093
  have eq72107 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq72098 eq13
    | (have r₁ := eq13 (σ x) (σ (M.op x y))
       have r₂ := eq72098
       grind)
    | exact resolve eq13 eq72098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72121 : (σ x) = (k (σ x) (σ (M.op x y))) := by grind
  clear eq72107
  have eq72129 : (τ (σ x)) = (k x (M.op x y)) := by
    first
    | exact superpose eq72121 eq63
    | exact resolve eq63 eq72121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq72146 : (τ (σ x)) = (k x y) := by
    first
    | exact superpose eq70868 eq72129
    | exact resolve eq72129 eq70868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70868 eq72129
  have eq72149 : x = (k x y) := by
    first
    | exact superpose eq28 eq72146
    | exact resolve eq72146 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq72146
  have eq73054 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13927 X0 X1
       have i₂ := eq8187 X0 (M.op X0 X1)
       grind)
    | exact superpose eq8187 eq13927
    | exact resolve eq13927 eq8187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8187 eq13927
  have eq73821 : (M.op (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq72098 eq73054
    | exact resolve eq73054 eq72098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74549 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq72098 eq73821
    | exact resolve eq73821 eq72098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72098 eq73821
  have eq75046 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq74549 eq945
    | exact resolve eq945 eq74549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75058 : ∀ X0 : G, (M.op (σ x) (σ (M.op x y))) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq74549 eq13882
    | exact resolve eq13882 eq74549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13882
  have eq75059 : ∀ X0 : G, (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq74549 eq13896
    | exact resolve eq13896 eq74549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13896
  have eq75089 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq74549 eq20428
    | exact resolve eq20428 eq74549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20428 eq74549
  have eq75091 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq71148 eq75089
    | exact resolve eq75089 eq71148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75089
  have eq75099 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq75058 x
       have i₂ := eq73054 sF2 x
       grind)
    | exact superpose eq73054 eq75058
    | exact resolve eq75058 eq73054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75058
  have eq75109 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq71148 eq75099
    | exact resolve eq75099 eq71148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75099
  have eq75582 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq75109 eq938
    | exact resolve eq938 eq75109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938
  have eq75687 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq75091 eq75582
    | exact resolve eq75582 eq75091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75582
  have eq77468 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq75687 eq945
    | exact resolve eq945 eq75687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq75687
  have eq77600 : (k (σ x) (k (σ x) (σ y))) = (σ (M.op (k x y) x)) ∨ (k x y) = (M.op x (k x y)) := by
    first
    | exact superpose eq59 eq270
    | exact resolve eq270 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq270
  have eq77725 : (k (σ x) (k (σ x) (σ y))) = (σ (M.op x x)) ∨ (k x y) = (M.op x (k x y)) := by
    first
    | (have i₁ := eq77600
       have i₂ := eq72149
       grind)
    | exact superpose eq72149 eq77600
    | exact resolve eq77600 eq72149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77600
  have eq77754 : (σ y) = (k (σ x) (k (σ x) (σ y))) ∨ (k x y) = (M.op x (k x y)) := by
    first
    | (have i₁ := eq77725
       have i₂ := eq71145
       grind)
    | exact superpose eq71145 eq77725
    | exact resolve eq77725 eq71145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77725
  have eq77774 : (σ y) = (k (σ x) (k (σ x) (σ (M.op x y)))) ∨ (k x y) = (M.op x (k x y)) := by
    first
    | exact superpose eq71144 eq77754
    | exact resolve eq77754 eq71144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77754
  have eq77779 : (σ y) = (k (σ x) (σ x)) ∨ (k x y) = (M.op x (k x y)) := by
    first
    | exact superpose eq72121 eq77774
    | exact resolve eq77774 eq72121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72121 eq77774
  have eq77783 : (σ y) = (k (σ x) (σ x)) ∨ (k x y) = (M.op x (k x y)) := by
    first
    | (have i₁ := eq77779
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq77779
    | exact resolve eq77779 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77779
  have eq77787 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (k x y) = (M.op x (k x y)) := by
    first
    | exact superpose eq71144 eq77783
    | exact resolve eq77783 eq71144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77783
  have eq77790 : x = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq77787
       have i₂ := eq72149
       grind)
    | exact superpose eq72149 eq77787
    | exact resolve eq77787 eq72149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72149 eq77787
  have eq77793 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq77790
       have i₂ := eq71145
       grind)
    | exact superpose eq71145 eq77790
    | exact resolve eq77790 eq71145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71145 eq77790
  have eq84143 : ∀ X0 : G, (σ x) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq75109 eq7795
    | (have j0 := eq7795 X0
       grind)
    | exact resolve eq7795 eq75109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7795
  have eq84234 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq77793 eq84143
    | exact resolve eq84143 eq77793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77793 eq84143
  have eq84253 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq75059 eq84234
    | exact resolve eq84234 eq75059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75059 eq84234
  have eq84261 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq75109 eq84253
    | exact resolve eq84253 eq75109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84253
  have eq84262 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq84261
  have eq84291 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (σ y)) = (M.op (σ x) (M.op (σ x) X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq84262 eq916
    | exact resolve eq916 eq84262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916 eq84262
  have eq84576 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq84291 x
       have i₂ := eq73054 sF2 x
       grind)
    | exact superpose eq73054 eq84291
    | exact resolve eq84291 eq73054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73054 eq84291
  have eq84635 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq71144 eq84576
    | exact resolve eq84576 eq71144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84576
  have eq84676 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ (M.op x y))) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq84635
       have i₂ := eq13947 sF2 sF1
       grind)
    | exact superpose eq13947 eq84635
    | exact resolve eq84635 eq13947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13947 eq84635
  have eq84703 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y := by
    first
    | exact superpose eq71148 eq84676
    | exact resolve eq84676 eq71148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71148 eq84676
  have eq84715 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq75091 eq84703
    | exact resolve eq84703 eq75091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75091 eq84703
  have eq84720 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq75109 eq84715
    | exact resolve eq84715 eq75109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75109 eq84715
  have eq84724 : x = y := by
    first
    | (have r₁ := eq84720
       have r₂ := eq27
       grind)
    | exact resolve eq84720 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84720
  have eq84730 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq84724
       grind)
    | exact superpose eq84724 eq24
    | exact resolve eq24 eq84724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq84724
  have eq85289 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq71144 eq84730
    | exact resolve eq84730 eq71144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71144 eq84730
  have eq85501 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq85289
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq85289
    | exact resolve eq85289 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq85289
  have eq87673 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq85501 eq75046
    | exact resolve eq75046 eq85501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75046 eq85501
  have eq87695 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq77468 eq87673
    | exact resolve eq87673 eq77468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77468 eq87673
  have eq87838 : False := by grind
  exact eq87838

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pyy_x_pxy_Equation2666 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X0 := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq21
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
  have eq47 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X3 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : y ≠ (M.op x y) ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq74 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq82 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq74
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq75
    | exact resolve eq75 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq84
    | exact resolve eq84 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq118 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq154 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq156 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq118
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq118
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq118 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq118 eq16
    | exact resolve eq16 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq156
  have eq204 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq42
    | (have j1 := eq11 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq42 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq209 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq47 eq14
    | exact resolve eq14 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq48
    | (have j0 := eq48 (σ y)
       grind)
    | exact resolve eq48 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq48 eq14
    | exact resolve eq14 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq497 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4)) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq499 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) X2)) y) := by
    intro X0 X1 X2
    first
    | exact superpose eq47 eq49
    | exact resolve eq49 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq500 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) X2)) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq48 eq49
    | exact resolve eq49 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq507 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq516 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X0 X1 X2 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) = (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4) (M.op (M.op X0 X1) (M.op X0 X2))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4 X1
       have i₂ := eq49 X0 X1 X2 X3
       grind)
    | exact superpose eq49 eq14
    | exact resolve eq14 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq648 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X0 X1 X2 (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4)
       have i₂ := eq49 (M.op (M.op X0 X1) (M.op X0 X2)) X0 X3 X4
       grind)
    | exact superpose eq49 eq52
    | exact resolve eq52 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq726 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) (σ X1) X2
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq14
    | (have j1 := eq71 X0 X1
       grind)
    | exact resolve eq14 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq732 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq908 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) y) := by
    intro X0
    first
    | (have i₁ := eq516 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq516
    | (have j0 := eq516 x y X0
       grind)
    | exact resolve eq516 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq909 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq516
    | (have j0 := eq516 (σ x) (σ y) X0
       grind)
    | exact resolve eq516 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq913 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4) (M.op (M.op X0 X1) (M.op X0 X2))) = (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq516 (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4 X1
       have i₂ := eq49 X0 X1 X2 X3
       grind)
    | exact superpose eq49 eq516
    | exact resolve eq516 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq921 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq516 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq516
    | (have j0 := eq516 x X0 y
       grind)
    | exact resolve eq516 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq922 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq516
    | (have j0 := eq516 (σ x) X0 (σ y)
       grind)
    | exact resolve eq516 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq926 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq516 X0 X1 x
       grind)
    | exact superpose eq516 eq14
    | exact resolve eq14 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq930 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op (M.op X0 X0) X1) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq949 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4) (M.op (M.op X0 X1) (M.op X0 X2))) = (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq913 X0 X1 X2 X3 X4
       have i₂ := eq516 X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)
       grind)
    | exact superpose eq516 eq913
    | exact resolve eq913 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq969 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X3)) X4) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X3)) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq949 X0 X1 x X3 X4
       have i₂ := eq516 X0 X1 x
       grind)
    | exact superpose eq516 eq949
    | exact resolve eq949 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq987 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq926 X0 (M.op X0 X1)
       have i₂ := eq516 X0 X0 X1
       grind)
    | exact superpose eq516 eq926
    | exact resolve eq926 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq988 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq926 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq926 X0 (M.op X0 X0)
       grind)
    | exact superpose eq926 eq926
    | exact resolve eq926 eq926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq992 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1 X1 X0
       have i₂ := eq926 (M.op X0 X1) X0
       grind)
    | exact superpose eq926 eq52
    | exact resolve eq52 eq926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq997 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X1
       have i₂ := eq926 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq926 eq14
    | exact resolve eq14 eq926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1012 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq992 X0 X1
       have i₂ := eq516 X0 X1 X1
       grind)
    | exact superpose eq516 eq992
    | exact resolve eq992 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1095 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq921 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq921
    | (have j0 := eq921 y
       grind)
    | exact resolve eq921 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1129 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1095
       have i₂ := eq908 X0
       grind)
    | exact superpose eq908 eq1095
    | exact resolve eq1095 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1258 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq27 eq922
    | (have j0 := eq922 (σ y)
       grind)
    | exact resolve eq922 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1292 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq909 eq1258
    | exact resolve eq1258 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1393 : (M.op x x) = (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op x x)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq987 (M.op x x) y
       have i₂ := eq1095
       grind)
    | exact superpose eq1095 eq987
    | exact resolve eq987 eq1095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1397 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq209 eq987
    | exact resolve eq987 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1399 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1258 eq987
    | exact resolve eq987 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258
  have eq1403 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq216 eq987
    | exact resolve eq987 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1429 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq1403
       have i₂ := eq926 sF4 (M.op sF4 sF4)
       grind)
    | exact superpose eq926 eq1403
    | exact resolve eq1403 eq926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403
  have eq1433 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1399
       have i₂ := eq926 sF2 (M.op sF2 sF2)
       grind)
    | exact superpose eq926 eq1399
    | exact resolve eq1399 eq926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399
  have eq1435 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq1397
       have i₂ := eq926 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq926 eq1397
    | exact resolve eq1397 eq926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397
  have eq1439 : (M.op x x) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1393
       have i₂ := eq926 x (M.op x x)
       grind)
    | exact superpose eq926 eq1393
    | exact resolve eq1393 eq926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393
  have eq1514 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1429 eq216
    | exact resolve eq216 eq1429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1526 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq1429 eq516
    | exact resolve eq516 eq1429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1530 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq1526 x
       have i₂ := eq516 sF4 sF2 x
       grind)
    | exact superpose eq516 eq1526
    | exact resolve eq1526 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526
  have eq1533 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq1429 eq1530
    | exact resolve eq1530 eq1429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1530
  have eq1536 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq1435 eq209
    | exact resolve eq209 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1548 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) x) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq1435 eq516
    | exact resolve eq516 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1552 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq1548 x
       have i₂ := eq516 sF0 x x
       grind)
    | exact superpose eq516 eq1548
    | exact resolve eq1548 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548
  have eq1555 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq1435 eq1552
    | exact resolve eq1552 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552
  have eq1681 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq1429 eq1433
    | exact resolve eq1433 eq1429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1433
  have eq1682 : (M.op x x) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq1435 eq1439
    | exact resolve eq1439 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq2214 : ∀ X0 : G, (M.op (M.op (M.op x y) x) X0) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1435 eq1012
    | exact resolve eq1012 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2216 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1012 (M.op X0 X1) X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq1012
    | exact resolve eq1012 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2218 : x = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | exact superpose eq209 eq1012
    | exact resolve eq1012 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2220 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq216 eq1012
    | exact resolve eq1012 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2224 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1012 (M.op (M.op X0 X0) X0) (M.op X0 X1)
       have i₂ := eq987 X0 X1
       grind)
    | exact superpose eq987 eq1012
    | exact resolve eq1012 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2245 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq926 X0 X1
       have i₂ := eq1012 X0 X1
       grind)
    | (have i₁ := eq926 X1 X1
       have i₂ := eq1012 X1 X1
       grind)
    | exact superpose eq1012 eq926
    | exact resolve eq926 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2298 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2224 X0 X1
       have i₂ := eq997 X0 X0
       grind)
    | exact superpose eq997 eq2224
    | exact resolve eq2224 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2224
  have eq2304 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2298 X0 X1
       have i₂ := eq516 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq516 eq2298
    | exact resolve eq2298 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2298
  have eq2305 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2304 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq2304
    | exact resolve eq2304 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2304
  have eq2365 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) y) X0) x) = (M.op (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) X0) := by
    intro X0
    first
    | exact superpose eq2218 eq516
    | exact resolve eq516 eq2218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2368 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) y) X0) x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) y) X0) := by
    intro X0
    first
    | (have i₁ := eq2365 X0
       have i₂ := eq516 sF0 y y
       grind)
    | exact superpose eq516 eq2365
    | exact resolve eq2365 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2365
  have eq2373 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) y) X0) x) := by
    intro X0
    first
    | exact superpose eq209 eq2368
    | exact resolve eq2368 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq2368
  have eq2384 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq2220 eq516
    | exact resolve eq516 eq2220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2387 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq2384 X0
       have i₂ := eq516 sF4 sF3 sF3
       grind)
    | exact superpose eq516 eq2384
    | exact resolve eq2384 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2384
  have eq2392 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq216 eq2387
    | exact resolve eq2387 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq2387
  have eq2662 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq2305 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2305
    | (have j0 := eq2305 x y
       grind)
    | exact resolve eq2305 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2668 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq2305
    | (have j0 := eq2305 (σ x) (σ y)
       grind)
    | exact resolve eq2305 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3552 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) y) := by
    intro X1
    first
    | exact superpose eq1129 eq212
    | (have j0 := eq212 y X1
       grind)
    | exact resolve eq212 eq1129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq3553 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) y) := by
    intro X1
    first
    | exact superpose eq1435 eq3552
    | exact resolve eq3552 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3552
  have eq3601 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2216 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq2216 X0 X1
       grind)
    | exact superpose eq2216 eq2216
    | exact resolve eq2216 eq2216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3607 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq3553 eq2216
    | exact resolve eq2216 eq3553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3553
  have eq3616 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq2218 eq2216
    | exact resolve eq2216 eq2218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2218
  have eq3627 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq2220 eq2216
    | exact resolve eq2216 eq2220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3662 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2305 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq2216 X0 X1
       grind)
    | exact superpose eq2216 eq2305
    | exact resolve eq2305 eq2216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3663 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3662 X0 X1
       have i₂ := eq516 (M.op X0 X1) X1 X1
       grind)
    | exact superpose eq516 eq3662
    | exact resolve eq3662 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3662
  have eq3683 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq3627
       have i₂ := eq1012 sF2 sF4
       grind)
    | exact superpose eq1012 eq3627
    | exact resolve eq3627 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3627
  have eq3692 : (M.op (M.op x y) y) = (M.op (M.op x x) (M.op x y)) := by
    first
    | (have i₁ := eq3616
       have i₂ := eq1012 x sF0
       grind)
    | exact superpose eq1012 eq3616
    | exact resolve eq3616 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3616
  have eq3700 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op x (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq1536 eq3607
    | exact resolve eq3607 eq1536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536 eq3607
  have eq3704 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3601 X0 X1
       have i₂ := eq1012 X0 (M.op X0 X1)
       grind)
    | exact superpose eq1012 eq3601
    | exact resolve eq3601 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3601
  have eq3718 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3663 X0 X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq3663
    | exact resolve eq3663 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3663
  have eq3730 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq922 eq3683
    | exact resolve eq3683 eq922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922 eq3683
  have eq3735 : (M.op (M.op x y) y) = (M.op (M.op x x) x) := by
    first
    | exact superpose eq921 eq3692
    | exact resolve eq3692 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921 eq3692
  have eq3739 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op (M.op x y) x) X0)) := by
    intro X0
    first
    | exact superpose eq1682 eq3700
    | exact resolve eq3700 eq1682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1682 eq3700
  have eq3741 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3704 X0 X1
       have i₂ := eq516 X0 X0 X1
       grind)
    | exact superpose eq516 eq3704
    | exact resolve eq3704 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3704
  have eq3937 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq3730 eq987
    | exact resolve eq987 eq3730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3939 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq3730 eq997
    | exact resolve eq997 eq3730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq4134 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1292 eq219
    | (have j0 := eq219 (σ y) X1
       grind)
    | exact resolve eq219 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq4135 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1429 eq4134
    | exact resolve eq4134 eq1429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4134
  have eq4192 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq4135 eq2216
    | exact resolve eq2216 eq4135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4135
  have eq4198 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq1514 eq4192
    | exact resolve eq4192 eq1514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4192
  have eq4205 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq1681 eq4198
    | exact resolve eq4198 eq1681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1681 eq4198
  have eq5921 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq154 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq154
    | (have j0 := eq154 x
       grind)
    | exact resolve eq154 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq5941 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5921
  have eq5946 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5941
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq5941
    | exact resolve eq5941 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5941
  have eq5963 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2214 eq3739
    | exact resolve eq3739 eq2214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2214
  have eq6026 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3741 X0 X2
       have i₂ := eq3741 X0 X1
       grind)
    | (have i₁ := eq3741 X1 X1
       have i₂ := eq3741 X1 X1
       grind)
    | exact superpose eq3741 eq3741
    | exact resolve eq3741 eq3741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6030 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq3741 x X0
       have i₂ := eq3735
       grind)
    | exact superpose eq3735 eq3741
    | exact resolve eq3741 eq3735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3735
  have eq6031 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq3730 eq3741
    | exact resolve eq3741 eq3730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3730
  have eq6079 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq987 X0 X2
       have i₂ := eq3741 X0 X1
       grind)
    | (have i₁ := eq987 X1 X1
       have i₂ := eq3741 X1 X1
       grind)
    | exact superpose eq3741 eq987
    | exact resolve eq987 eq3741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987 eq3741
  have eq6290 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) y) (M.op (M.op x X0) X1)) = (M.op (M.op (M.op x X0) (M.op x X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq516 (M.op x X0) X0 X1
       have i₂ := eq6030 X0
       grind)
    | (have i₁ := eq516 (M.op x y) y x
       have i₂ := eq6030 X0
       grind)
    | exact superpose eq6030 eq516
    | exact resolve eq516 eq6030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6302 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) y) (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6290 X0 X1
       have i₂ := eq14 x X0 X0
       grind)
    | exact superpose eq14 eq6290
    | exact resolve eq6290 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6290
  have eq6363 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) X0) X1)) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) X0)) X0) := by
    intro X0 X1
    first
    | exact superpose eq6031 eq516
    | exact resolve eq516 eq6031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6375 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6363 x X1
       have i₂ := eq14 sF2 x x
       grind)
    | exact superpose eq14 eq6363
    | exact resolve eq6363 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6363
  have eq6514 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq204
    | (have j0 := eq204 (M.op x y)
       grind)
    | exact resolve eq204 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq6532 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq6514
  have eq6535 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq118 eq6532
    | exact resolve eq6532 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq6532
  have eq7658 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq732
  have eq8639 : ∀ X0 : G, x = (M.op (M.op (M.op x x) x) (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq5963 eq2245
    | exact resolve eq2245 eq5963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2245 eq5963
  have eq8644 : ∀ X0 : G, x = (M.op (M.op (M.op x y) y) (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq8639 X0
       have i₂ := eq6030 x
       grind)
    | exact superpose eq6030 eq8639
    | exact resolve eq8639 eq6030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8639
  have eq8776 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1129 eq499
    | (have j0 := eq499 y X1 X2
       grind)
    | exact resolve eq499 eq1129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499 eq1129
  have eq8777 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) x) X1)) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1435 eq8776
    | exact resolve eq8776 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8776
  have eq8778 : ∀ X2 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x x) X2)) y) := by
    intro X2
    first
    | exact superpose eq3739 eq8777
    | exact resolve eq8777 eq3739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3739 eq8777
  have eq9821 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x y) (M.op x X0))) y) := by
    intro X0
    first
    | (have i₁ := eq8778 y
       have i₂ := eq908 X0
       grind)
    | exact superpose eq908 eq8778
    | exact resolve eq8778 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908 eq8778
  have eq9864 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) y) := by
    first
    | (have i₁ := eq9821 x
       have i₂ := eq516 sF0 x (M.op x x)
       grind)
    | exact superpose eq516 eq9821
    | exact resolve eq9821 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9821
  have eq9882 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) y) := by
    first
    | (have i₁ := eq9864
       have i₂ := eq1012 sF0 x
       grind)
    | exact superpose eq1012 eq9864
    | exact resolve eq9864 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9864
  have eq9895 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) x) y) := by
    first
    | exact superpose eq1555 eq9882
    | exact resolve eq9882 eq1555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555 eq9882
  have eq9909 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1292 eq500
    | (have j0 := eq500 (σ y) X1 X2
       grind)
    | exact resolve eq500 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500 eq1292
  have eq9910 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1429 eq9909
    | exact resolve eq9909 eq1429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429 eq9909
  have eq9911 : ∀ X2 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ x)) X2)) (σ y)) := by
    intro X2
    first
    | exact superpose eq4205 eq9910
    | exact resolve eq9910 eq4205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4205 eq9910
  have eq9916 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) (σ y)) := by
    intro X0
    first
    | exact superpose eq909 eq9911
    | exact resolve eq9911 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909 eq9911
  have eq9959 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq9916 x
       have i₂ := eq516 sF4 sF2 (M.op sF2 x)
       grind)
    | exact superpose eq516 eq9916
    | exact resolve eq9916 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9916
  have eq9977 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq9959
       have i₂ := eq1012 sF4 sF2
       grind)
    | exact superpose eq1012 eq9959
    | exact resolve eq9959 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9959
  have eq9990 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1533 eq9977
    | exact resolve eq9977 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533 eq9977
  have eq10004 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) X0) X0) y) := by
    intro X0
    first
    | (have i₁ := eq9895
       have i₂ := eq6026 sF0 x x
       grind)
    | (have i₁ := eq9895
       have i₂ := eq6026 sF0 x x
       grind)
    | exact superpose eq6026 eq9895
    | exact resolve eq9895 eq6026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9895
  have eq10045 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9990
       have i₂ := eq6026 sF4 sF2 x
       grind)
    | (have i₁ := eq9990
       have i₂ := eq6026 sF4 x sF2
       grind)
    | exact superpose eq6026 eq9990
    | exact resolve eq9990 eq6026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6026 eq9990
  have eq12709 : ∀ X0 X1 : G, (M.op x x) = (M.op x (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq6302 eq2373
    | exact resolve eq2373 eq6302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2373 eq6302
  have eq12991 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq6375 eq2392
    | exact resolve eq2392 eq6375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2392 eq6375
  have eq14634 : ∀ X0 : G, (σ x) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq726 x x X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq726
    | (have j0 := eq726 x x x
       grind)
    | exact resolve eq726 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq14774 : ∀ X0 : G, (σ x) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq14634 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14634
  have eq14809 : ∀ X0 : G, (σ x) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14774 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14774
    | (have j0 := eq14774 X0
       grind)
    | exact resolve eq14774 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14774
  have eq14865 : ∀ X0 : G, (σ x) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14809 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14809
    | (have j0 := eq14809 X0
       grind)
    | exact resolve eq14809 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14809
  have eq15273 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X0 X0) X1) X3)) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X3)) X4)) X1) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq497 X0 X1 x X3 X4
       have i₂ := eq516 X0 X1 x
       grind)
    | exact superpose eq516 eq497
    | exact resolve eq497 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq15386 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X2))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15273 X0 X1 X2 (M.op X0 x)
       have i₂ := eq516 X0 (M.op (M.op (M.op X0 X0) X1) X2) x
       grind)
    | exact superpose eq516 eq15273
    | exact resolve eq15273 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15273
  have eq15434 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15386 X0 X1 X2
       have i₂ := eq14 (M.op X0 X0) X1 (M.op (M.op (M.op X0 X0) X1) X2)
       grind)
    | exact superpose eq14 eq15386
    | exact resolve eq15386 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15386
  have eq15597 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) X3) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq507 X0 X1 x X3 X4
       have i₂ := eq516 X0 X1 x
       grind)
    | exact superpose eq516 eq507
    | exact resolve eq507 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq15707 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) (M.op (M.op X0 X0) (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15597 X0 (M.op X0 X1) X2 X2
       have i₂ := eq52 X0 X0 X1 X2
       grind)
    | exact superpose eq52 eq15597
    | exact resolve eq15597 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq15737 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0) X3) X2
       have i₂ := eq15597 X0 X1 (M.op (M.op (M.op X0 X0) X1) X2) X3
       grind)
    | exact superpose eq15597 eq14
    | exact resolve eq14 eq15597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15597
  have eq15784 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15737 X0 X1 X2 x
       have i₂ := eq2305 (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0) x
       grind)
    | exact superpose eq2305 eq15737
    | exact resolve eq15737 eq2305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15737
  have eq15806 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15707 X0 X1 X2
       have i₂ := eq516 (M.op X0 X0) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq516 eq15707
    | exact resolve eq15707 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15707
  have eq15897 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15784 X0 X1 X2
       have i₂ := eq516 (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0 X0
       grind)
    | exact superpose eq516 eq15784
    | exact resolve eq15784 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15784
  have eq15915 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15806 X0 X1 X2
       have i₂ := eq516 X0 X0 X0
       grind)
    | exact superpose eq516 eq15806
    | exact resolve eq15806 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15806
  have eq15969 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0) (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15897 X0 X1 X2
       have i₂ := eq1012 (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0
       grind)
    | exact superpose eq1012 eq15897
    | exact resolve eq15897 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15897
  have eq15984 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15915 X0 X1 X2
       have i₂ := eq6079 X0 X0 X1
       grind)
    | exact superpose eq6079 eq15915
    | exact resolve eq15915 eq6079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15915
  have eq16011 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15969 X0 X1 X1
       have i₂ := eq2305 (M.op (M.op X0 X0) X1) X1
       grind)
    | exact superpose eq2305 eq15969
    | exact resolve eq15969 eq2305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15969
  have eq16023 : ∀ X0 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X0) X0) X2) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq15984 X0 x X2
       have i₂ := eq516 X0 X0 x
       grind)
    | exact superpose eq516 eq15984
    | exact resolve eq15984 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15984
  have eq16040 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) X0) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1)) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    have f16040_11 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1))) := by
      intro X0 X1
      grind
    have f16040_12 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) (M.op X0 X2)) := by
      intro X0 X1 X2
      grind
    have f16040_20 : (M.op (M.op X0 X0) X1) ≠ (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) X0) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1)) := by grind
    have f16040_22 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) X0) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1)) := by
      intro X0 X1
      first
      | (have i₁ := f16040_11 X0 x
         have i₂ := f16040_12 (M.op X0 X0) x x
         grind)
      | exact superpose f16040_12 f16040_11
      | exact resolve f16040_11 f16040_12
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16040_23 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) (M.op (M.op (M.op X0 X0) X0) X1)) := by
      intro X0 X1
      first
      | (have i₁ := f16040_22 x X1
         have i₂ := f16040_12 x x x
         grind)
      | exact superpose f16040_12 f16040_22
      | exact resolve f16040_22 f16040_12
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16040_177 : (M.op (M.op X0 X0) X1) ≠ (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) (M.op (M.op (M.op X0 X0) X0) X1)) := by
      first
      | (have i₁ := f16040_20
         have i₂ := f16040_12 X0 X0 X0
         grind)
      | exact superpose f16040_12 f16040_20
      | exact resolve f16040_20 f16040_12
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16040_179 : False := by
      first
      | (have r₁ := f16040_177
         have r₂ := f16040_23 X0 X1
         grind)
      | exact resolve f16040_177 f16040_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f16040_179
  clear eq16011
  have eq16056 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) (M.op (M.op (M.op X0 X0) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16040 x X1
       have i₂ := eq516 x x x
       grind)
    | exact superpose eq516 eq16040
    | exact resolve eq16040 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16040
  have eq16472 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X0 X0) X1) X3)) = (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X3)) X4) (M.op (M.op X0 X0) X1)) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq521 X0 X1 x X3 X4
       have i₂ := eq516 X0 X1 x
       grind)
    | exact superpose eq516 eq521
    | exact resolve eq521 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq20099 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq648 X0 X1 X2 X3 x
       have i₂ := eq2305 (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) x
       grind)
    | exact superpose eq2305 eq648
    | exact resolve eq648 eq2305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq20100 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0)) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20099 X0 X1 X2 X3
       have i₂ := eq516 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)
       grind)
    | exact superpose eq516 eq20099
    | exact resolve eq20099 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20099
  have eq20101 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op (M.op X0 X0) X1) X0)) (M.op (M.op (M.op X0 X0) X1) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20100 X0 X1 x X3
       have i₂ := eq516 X0 X1 x
       grind)
    | exact superpose eq516 eq20100
    | exact resolve eq20100 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20100
  have eq20102 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op X0 X0) X1) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20101 X0 X1 X3
       have i₂ := eq516 (M.op (M.op X0 X0) X1) X0 X0
       grind)
    | exact superpose eq516 eq20101
    | exact resolve eq20101 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20101
  have eq20103 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op X0 X0) X1)) (M.op (M.op (M.op X0 X0) X1) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20102 X0 X1 X3
       have i₂ := eq1012 (M.op (M.op X0 X0) X1) X0
       grind)
    | exact superpose eq1012 eq20102
    | exact resolve eq20102 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20102
  have eq20216 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 X0) X1))) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20103 (M.op X0 (M.op (M.op (M.op X0 X0) X1) x)) (M.op (M.op X0 X0) X1) (M.op X0 (M.op (M.op (M.op X0 X0) X1) x))
       have i₂ := eq16472 X0 X1 x (M.op X0 (M.op (M.op (M.op X0 X0) X1) x))
       grind)
    | exact superpose eq16472 eq20103
    | exact resolve eq20103 eq16472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16472 eq20103
  have eq20297 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20216 X0 X1 X2
       have i₂ := eq1012 (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 X0) X1))
       grind)
    | exact superpose eq1012 eq20216
    | exact resolve eq20216 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20216
  have eq20417 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20297 X0 X1 X2
       have i₂ := eq2305 (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq2305 eq20297
    | exact resolve eq20297 eq2305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20297
  have eq20520 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20417 X0 X1 X2
       have i₂ := eq516 (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))
       grind)
    | exact superpose eq516 eq20417
    | exact resolve eq20417 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20417
  have eq20579 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X2)) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20520 X0 X1 X2
       have i₂ := eq516 X0 (M.op (M.op (M.op X0 X0) X1) X2) (M.op (M.op (M.op X0 X0) X1) X2)
       grind)
    | exact superpose eq516 eq20520
    | exact resolve eq20520 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20520
  have eq20612 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op (M.op X0 X0) X1) X2)) = (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20579 X0 X1 X2
       have i₂ := eq516 (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X2) X1
       grind)
    | exact superpose eq516 eq20579
    | exact resolve eq20579 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20579
  have eq20631 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X1) X2)) = (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20612 X0 X1 X2
       have i₂ := eq516 X0 X0 X0
       grind)
    | exact superpose eq516 eq20612
    | exact resolve eq20612 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20612
  have eq30135 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq87 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30144 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq30135
    | exact resolve eq30135 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30135
  have eq30149 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq30144
       have r₂ := eq28
       grind)
    | exact resolve eq30144 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30144
  have eq30151 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq30149
    | exact resolve eq30149 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30149
  have eq30153 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq30151
  have eq30225 : (τ (σ x)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30153 eq60
    | exact resolve eq60 eq30153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30153
  have eq30239 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq30225
    | exact resolve eq30225 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30225
  have eq30243 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq30239
       have r₂ := eq65
       grind)
    | exact resolve eq30239 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq30239
  have eq30366 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq30243
       grind)
    | exact superpose eq30243 eq45
    | exact resolve eq45 eq30243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30373 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq30243
       grind)
    | exact superpose eq30243 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq30243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30243
  have eq30381 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq30373
  have eq30389 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30381
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq30381
    | exact resolve eq30381 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30381
  have eq30396 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq30366
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30366
    | exact resolve eq30366 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30366
  have eq30403 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30389
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq30389
    | exact resolve eq30389 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30389
  have eq30451 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30396 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq30396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30396
  have eq30464 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq30451
    | exact resolve eq30451 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30451
  have eq30470 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq30464
    | exact resolve eq30464 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30464
  have eq30471 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq30470
  have eq30658 : x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq30659 : ∀ X0 : G, y = (M.op (M.op x X0) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq926 y X0
       have i₂ := eq30403
       grind)
    | exact superpose eq30403 eq926
    | exact resolve eq926 eq30403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30692 : y = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2216 y y
       have i₂ := eq30403
       grind)
    | exact superpose eq30403 eq2216
    | exact resolve eq2216 eq30403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30403
  have eq30709 : y = (M.op (M.op x x) y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30692
       have i₂ := eq1012 x y
       grind)
    | exact superpose eq1012 eq30692
    | exact resolve eq30692 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30692
  have eq30717 : y = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30659 x
       have i₂ := eq6030 x
       grind)
    | (have i₁ := eq30659 y
       have i₂ := eq6030 x
       grind)
    | exact superpose eq6030 eq30659
    | (have j0 := eq30659 y
       grind)
    | exact resolve eq30659 eq6030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6030 eq30659
  have eq30720 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30709
       have i₂ := eq1095
       grind)
    | exact superpose eq1095 eq30709
    | exact resolve eq30709 eq1095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095 eq30709
  have eq30724 : y = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1435 eq30720
    | exact resolve eq30720 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30720
  have eq31568 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq30658
       grind)
    | exact superpose eq30658 eq45
    | exact resolve eq45 eq30658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq30658
  have eq31595 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31568
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31568
    | exact resolve eq31568 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31568
  have eq31877 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) X0) X0) y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30717 eq6079
    | exact resolve eq6079 eq30717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30717
  have eq31881 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10004 eq31877
    | exact resolve eq31877 eq10004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31877
  have eq32816 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1435 eq164
    | exact resolve eq164 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq32817 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1435 eq32816
    | exact resolve eq32816 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435 eq32816
  have eq32891 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31595 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq31595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31595
  have eq32904 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq32891
    | exact resolve eq32891 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32891
  have eq32910 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq32904
    | exact resolve eq32904 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32904
  have eq32911 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq32910
  have eq32916 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq82
       have i₂ := eq31881
       grind)
    | exact superpose eq31881 eq82
    | exact resolve eq82 eq31881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31881
  have eq32996 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32916
  have eq33035 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq32996
    | exact resolve eq32996 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32996
  have eq33288 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5946 eq33035
    | exact resolve eq33035 eq5946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34185 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq30471 eq926
    | exact resolve eq926 eq30471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30471
  have eq34243 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq6031 eq34185
    | (have j0 := eq34185 (σ y)
       grind)
    | exact resolve eq34185 eq6031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34185
  have eq39291 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq34243 eq6079
    | exact resolve eq6079 eq34243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34243
  have eq39295 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq10045 eq39291
    | exact resolve eq39291 eq10045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39291
  have eq39319 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30724 eq32817
    | exact resolve eq32817 eq30724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30724 eq32817
  have eq39383 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq39319
  have eq39390 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39383
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq39383
    | exact resolve eq39383 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39383
  have eq39423 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq6535 eq39390
    | exact resolve eq39390 eq6535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6535
  have eq39427 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39390 eq159
    | exact resolve eq159 eq39390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39390
  have eq39452 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq39427
    | exact resolve eq39427 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39427
  have eq41834 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq39295 eq926
    | exact resolve eq926 eq39295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39295
  have eq44220 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq32911 eq926
    | exact resolve eq926 eq32911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32911
  have eq44281 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6031 eq44220
    | (have j0 := eq44220 (σ y)
       grind)
    | exact resolve eq44220 eq6031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44220
  have eq45872 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq44281 eq6079
    | exact resolve eq6079 eq44281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44281
  have eq45876 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10045 eq45872
    | exact resolve eq45872 eq10045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45872
  have eq175915 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq39423 eq988
    | exact resolve eq988 eq39423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988 eq39423
  have eq189613 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq45876 eq33288
    | exact resolve eq33288 eq45876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45876
  have eq189677 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  have eq189744 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq33288
  have eq189758 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq189613
  have eq189826 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq189758
       have r₂ := eq28
       grind)
    | exact resolve eq189758 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189758
  have eq190257 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq189826 eq28
    | exact resolve eq28 eq189826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190282 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq189826 eq2668
    | exact resolve eq2668 eq189826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190313 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ y) X0) X0) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq189826 eq10045
    | exact resolve eq10045 eq189826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189826
  have eq190327 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq190313 x
       have i₂ := eq3718 sF3 x
       grind)
    | exact superpose eq3718 eq190313
    | exact resolve eq190313 eq3718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190313
  have eq190331 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq190282
    | exact resolve eq190282 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190282
  have eq191346 : (σ x) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq190331 eq14865
    | (have j0 := eq14865 (σ y)
       grind)
    | exact resolve eq14865 eq190331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14865 eq190331
  have eq191430 : (σ x) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq191346
  have eq194702 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) (M.op (M.op (M.op X0 X0) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16056 X0 X1
       have i₂ := eq16023 X0 X1
       grind)
    | exact superpose eq16023 eq16056
    | exact resolve eq16056 eq16023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16023 eq16056
  have eq222136 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq191430 eq2216
    | exact resolve eq2216 eq191430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191430
  have eq222164 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6031 eq222136
    | exact resolve eq222136 eq6031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222136
  have eq252968 : (k (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq222164 eq2216
    | exact resolve eq2216 eq222164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222164
  have eq252998 : (k (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2220 eq252968
    | exact resolve eq252968 eq2220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252968
  have eq253010 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3939 eq252998
    | exact resolve eq252998 eq3939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3939 eq252998
  have eq253475 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq253010 eq56
    | exact resolve eq56 eq253010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253010
  have eq253581 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq190327 eq253475
    | exact resolve eq253475 eq190327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190327 eq253475
  have eq253905 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq253581
  have eq253919 : y = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq253905
    | exact resolve eq253905 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq253905
  have eq253923 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq253919
       grind)
    | exact superpose eq253919 eq44
    | exact resolve eq44 eq253919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq253919
  have eq254029 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq253923
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq253923
    | exact resolve eq253923 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253923
  have eq345119 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq189677 eq33035
    | exact resolve eq33035 eq189677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33035 eq189677
  have eq345277 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq345119
  have eq345296 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq345277
       have r₂ := eq189744
       grind)
    | exact resolve eq345277 eq189744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189744 eq345277
  have eq345395 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq345296 eq12991
    | exact resolve eq12991 eq345296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12991 eq345296
  have eq350558 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq175915 eq345395
    | exact resolve eq345395 eq175915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175915 eq345395
  have eq350691 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq350558
  have eq350729 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq350691
    | exact resolve eq350691 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350691
  have eq350743 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq350729
       have r₂ := eq28
       grind)
    | exact resolve eq350729 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350729
  have eq351153 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq350743
  have eq351283 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq351153 eq159
    | exact resolve eq159 eq351153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq351153
  have eq351382 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq351283
    | exact resolve eq351283 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351283
  have eq351771 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq351382 eq39452
    | exact resolve eq39452 eq351382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39452 eq351382
  have eq351845 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq351771
  have eq353099 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq351845 eq66
    | (have r₁ := eq66
       have r₂ := eq351845
       grind)
    | exact resolve eq66 eq351845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq353121 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq351845 eq2668
    | exact resolve eq2668 eq351845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2668
  have eq353125 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) X0)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq351845 eq3937
    | exact resolve eq3937 eq351845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3937
  have eq353156 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ y) X0) X0) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq351845 eq10045
    | exact resolve eq10045 eq351845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10045
  have eq353407 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq353099
  have eq353435 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq353156 x
       have i₂ := eq3718 sF3 x
       grind)
    | exact superpose eq3718 eq353156
    | exact resolve eq353156 eq3718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353156
  have eq353440 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq353121
    | exact resolve eq353121 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353121
  have eq353578 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq353435 eq926
    | exact resolve eq926 eq353435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq353590 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op (σ y) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq353435 eq1012
    | exact resolve eq1012 eq353435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353435
  have eq354268 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq353440
  have eq376274 : ∀ X0 : G, (σ x) = (k (σ x) (M.op (σ y) (M.op (σ x) X0))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq353125 eq930
    | exact resolve eq930 eq353125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930 eq353125
  have eq381879 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (σ y) (M.op (σ x) X0)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq353590 (M.op sF2 x)
       have i₂ := eq2305 sF2 x
       grind)
    | exact superpose eq2305 eq353590
    | exact resolve eq353590 eq2305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353590
  have eq382129 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (σ x) X0)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6031 eq381879
    | exact resolve eq381879 eq6031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6031 eq381879
  have eq398075 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X3)) X4) = (M.op (M.op (M.op X0 X0) X4) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq969 X0 X1 X3 X4
       have i₂ := eq15434 X0 X1 X3
       grind)
    | exact superpose eq15434 eq969
    | exact resolve eq969 eq15434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969 eq15434
  have eq398076 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X3)) X4) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq398075 X0 X1 X3 X4
       have i₂ := eq516 (M.op X0 X0) X4 X1
       grind)
    | exact superpose eq516 eq398075
    | exact resolve eq398075 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398075
  have eq398077 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X3)) X4) = (M.op (M.op (M.op X0 X0) X0) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq398076 X0 X1 X3 X4
       have i₂ := eq516 X0 X0 X0
       grind)
    | exact superpose eq516 eq398076
    | exact resolve eq398076 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516 eq398076
  have eq427488 : (σ x) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq382129 eq376274
    | exact resolve eq376274 eq382129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376274 eq382129
  have eq427632 : (σ x) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq427488
  have eq511208 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X1) X2)) = (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20631 X0 X1 X2
       have i₂ := eq398077 X0 X1 X2 (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))
       grind)
    | exact superpose eq398077 eq20631
    | exact resolve eq20631 eq398077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20631 eq398077
  have eq511209 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq511208 X0 X1 X2
       have i₂ := eq6079 X0 X0 (M.op (M.op (M.op X0 X0) X1) X2)
       grind)
    | exact superpose eq6079 eq511208
    | exact resolve eq511208 eq6079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6079 eq511208
  have eq512526 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq353407 eq60
    | exact resolve eq60 eq353407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq353407
  have eq512597 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq512526
    | exact resolve eq512526 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512526
  have eq515378 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq512597 eq353578
    | exact resolve eq353578 eq512597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353578 eq512597
  have eq515512 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (k x y) := by grind
  clear eq515378
  have eq515645 : x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq515512
    | exact resolve eq515512 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515512
  have eq515791 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq515645
       grind)
    | exact superpose eq515645 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq515645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515645
  have eq515816 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq515791
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq515791
    | exact resolve eq515791 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515791
  have eq515817 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq515816
  have eq515858 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq515817
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq515817
    | exact resolve eq515817 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515817
  have eq515859 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq515858
  have eq516838 : (M.op x y) = (M.op x (M.op (M.op x y) y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq194702 y y
       have i₂ := eq515859
       grind)
    | exact superpose eq515859 eq194702
    | exact resolve eq194702 eq515859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515859
  have eq516909 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq516838
       have i₂ := eq12709 y y
       grind)
    | exact superpose eq12709 eq516838
    | exact resolve eq516838 eq12709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516838
  have eq516954 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq516909
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq516909
    | exact resolve eq516909 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516909
  have eq518373 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq82
       have i₂ := eq516954
       grind)
    | exact superpose eq516954 eq82
    | exact resolve eq82 eq516954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516954
  have eq518611 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq518373
  have eq518683 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq518611
    | exact resolve eq518611 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518611
  have eq520819 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq518683 eq254029
    | exact resolve eq254029 eq518683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254029 eq518683
  have eq520912 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq520819
  have eq520964 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq520912
       have r₂ := eq190257
       grind)
    | exact resolve eq520912 eq190257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190257 eq520912
  have eq520977 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq520964 eq28
    | exact resolve eq28 eq520964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521112 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq520964 eq354268
    | exact resolve eq354268 eq520964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354268
  have eq521171 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq520964 eq427632
    | exact resolve eq427632 eq520964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427632 eq520964
  have eq521186 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq521171
  have eq521244 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq521112
  have eq521303 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq521186
    | exact resolve eq521186 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521186
  have eq524213 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq521244 eq56
    | exact resolve eq56 eq521244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq521244
  have eq524435 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq524213
    | exact resolve eq524213 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524213
  have eq524455 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq351845 eq521303
    | exact resolve eq521303 eq351845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351845 eq521303
  have eq524500 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq524455
  have eq537338 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq524435
       grind)
    | exact superpose eq524435 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq524435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524435
  have eq537367 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq537338
  have eq537532 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq524500 eq87
    | exact resolve eq87 eq524500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq524500
  have eq537572 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq537532
  have eq537588 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq537572
       have r₂ := eq520977
       grind)
    | exact resolve eq537572 eq520977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520977 eq537572
  have eq558099 : (M.op x y) = (M.op x (M.op (M.op x y) y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq194702 y y
       have i₂ := eq537588
       grind)
    | exact superpose eq537588 eq194702
    | exact resolve eq194702 eq537588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194702 eq537588
  have eq558170 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq558099
       have i₂ := eq12709 y y
       grind)
    | exact superpose eq12709 eq558099
    | exact resolve eq558099 eq12709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558099
  have eq558234 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq558170
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq558170
    | exact resolve eq558170 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558170
  have eq600442 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq537367
       have i₂ := eq558234
       grind)
    | exact superpose eq558234 eq537367
    | exact resolve eq537367 eq558234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537367 eq558234
  have eq600645 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq600442
  have eq600807 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq600645 eq21
    | exact resolve eq21 eq600645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq600961 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq600645 eq2662
    | exact resolve eq2662 eq600645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2662
  have eq601047 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op y X0) X0) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq600645 eq10004
    | exact resolve eq10004 eq600645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10004
  have eq601092 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq600645
  have eq601096 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq601047 x
       have i₂ := eq3718 y x
       grind)
    | exact superpose eq3718 eq601047
    | exact resolve eq601047 eq3718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3718 eq601047
  have eq601129 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq600961
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq600961
    | exact resolve eq600961 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600961
  have eq601251 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq600807
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq600807
    | exact resolve eq600807 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600807
  have eq602423 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq82
       have i₂ := eq601096
       grind)
    | exact superpose eq601096 eq82
    | exact resolve eq82 eq601096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601096
  have eq602720 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq602423
       have r₂ := eq601092
       grind)
    | exact resolve eq602423 eq601092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601092 eq602423
  have eq602736 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq602720
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq602720
    | exact resolve eq602720 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602720
  have eq602756 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq82
       have i₂ := eq601129
       grind)
    | exact superpose eq601129 eq82
    | exact resolve eq82 eq601129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq601129
  have eq602998 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq602756
  have eq603078 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq602998
    | exact resolve eq602998 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602998
  have eq606057 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5946 eq602736
    | exact resolve eq602736 eq5946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5946 eq602736
  have eq970638 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq606057 eq2305
    | exact resolve eq2305 eq606057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2305 eq606057
  have eq970751 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq970638
    | exact resolve eq970638 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970638
  have eq971008 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq970751
  have eq971481 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq971008 eq603078
    | exact resolve eq603078 eq971008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603078 eq971008
  have eq971636 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq971481
  have eq971744 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq971636 eq28
    | exact resolve eq28 eq971636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971636
  have eq972294 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq971744
       have r₂ := eq601251
       grind)
    | exact resolve eq971744 eq601251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601251 eq971744
  have eq972303 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq972294 eq29
    | exact resolve eq29 eq972294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq972294
  have eq973512 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq972303
    | exact resolve eq972303 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq972303
  have eq973513 : x = (M.op x y) := by grind
  clear eq973512
  have eq973517 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq973513 eq21
    | exact resolve eq21 eq973513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq973757 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op x X0) x)) := by
    intro X0
    first
    | exact superpose eq973513 eq8644
    | exact resolve eq8644 eq973513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8644
  have eq973960 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op x X0) x)) := by
    intro X0
    first
    | (have i₁ := eq973757 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq973757
    | (have j0 := eq973757 X0
       grind)
    | exact resolve eq973757 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973757
  have eq974125 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq973517
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq973517
    | exact resolve eq973517 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973517
  have eq974168 : ∀ X0 : G, x = (M.op x (M.op (M.op x X0) x)) := by
    intro X0
    first
    | exact superpose eq973513 eq973960
    | exact resolve eq973960 eq973513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973960
  have eq974220 : x = (M.op x x) := by
    first
    | (have i₁ := eq974168 x
       have i₂ := eq12709 x x
       grind)
    | exact superpose eq12709 eq974168
    | exact resolve eq974168 eq12709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974168
  have eq974332 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq974125 eq27
    | exact resolve eq27 eq974125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq974381 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq974125 eq1514
    | exact resolve eq1514 eq974125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1514
  have eq975344 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq7658 x
       have i₂ := eq974220
       grind)
    | exact superpose eq974220 eq7658
    | exact resolve eq7658 eq974220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7658
  have eq975462 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq975344
  have eq975463 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq975462
  have eq975530 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq975463
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq975463
    | exact resolve eq975463 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975463
  have eq975652 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq974125 eq975530
    | exact resolve eq975530 eq974125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975530
  have eq979024 : (M.op (M.op (σ (M.op x y)) (σ y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq974381 eq2216
    | exact resolve eq2216 eq974381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2216
  have eq979083 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq979024
       have i₂ := eq1012 sF1 sF3
       grind)
    | exact superpose eq1012 eq979024
    | exact resolve eq979024 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012 eq979024
  have eq979126 : (M.op (σ (M.op x y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq975652 eq979083
    | exact resolve eq979083 eq975652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975652 eq979083
  have eq979154 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq974332 eq979126
    | exact resolve eq979126 eq974332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979126
  have eq979211 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq979154 eq974381
    | exact resolve eq974381 eq979154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974381
  have eq979227 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq979154 eq41834
    | exact resolve eq41834 eq979154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41834
  have eq979344 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq979154 eq979227
    | exact resolve eq979227 eq979154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979227
  have eq979345 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq979344
  have eq979388 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq974125 eq979345
    | exact resolve eq979345 eq974125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979345
  have eq979416 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq979388
       have r₂ := eq28
       grind)
    | exact resolve eq979388 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979388
  have eq980301 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq979211 eq2220
    | exact resolve eq2220 eq979211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2220
  have eq980538 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq974125 eq980301
    | exact resolve eq980301 eq974125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980301
  have eq997794 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op x X0) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq511209 y X1 x
       have i₂ := eq979416
       grind)
    | exact superpose eq979416 eq511209
    | exact resolve eq511209 eq979416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511209 eq979416
  have eq997963 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op x X0) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq997794 X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq997794
    | (have j0 := eq997794 X0 X1
       grind)
    | exact resolve eq997794 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq997794
  have eq998028 : ∀ X0 X1 : G, y = (M.op x (M.op (M.op x X0) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq973513 eq997963
    | exact resolve eq997963 eq973513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973513 eq997963
  have eq998079 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq998028 x x
       have i₂ := eq12709 x x
       grind)
    | exact superpose eq12709 eq998028
    | exact resolve eq998028 eq12709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12709 eq998028
  have eq998114 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq998079
       have i₂ := eq974220
       grind)
    | exact superpose eq974220 eq998079
    | exact resolve eq998079 eq974220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974220 eq998079
  have eq998509 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq998114 eq980538
    | exact resolve eq980538 eq998114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980538 eq998114
  have eq998513 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq974332 eq998509
    | exact resolve eq998509 eq974332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974332 eq998509
  have eq998617 : x = y := by
    first
    | (have r₁ := eq998513
       have r₂ := eq28
       grind)
    | exact resolve eq998513 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998513
  have eq998708 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq998617
       grind)
    | exact superpose eq998617 eq25
    | exact resolve eq25 eq998617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq998617
  have eq999621 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq998708
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq998708
    | exact resolve eq998708 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq998708
  have eq999810 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq974125 eq999621
    | exact resolve eq999621 eq974125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974125 eq999621
  have eq1000795 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq999810 eq979211
    | exact resolve eq979211 eq999810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979211 eq999810
  have eq1000816 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq979154 eq1000795
    | exact resolve eq1000795 eq979154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979154 eq1000795
  have eq1001021 : False := by grind
  exact eq1001021

/-- `Equation2702`: `x = ((y ◇ x) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_y_pxy_Equation2702 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2702 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2702.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
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
  have eq32 : y = (τ (σ y)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq175 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X3)) X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq16 X0 (M.op (M.op x X0) (M.op X0 x)) X3
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, x = (M.op (M.op (M.op X0 x) (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq177 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq606 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
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
  have eq608 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X0) (k X0 X1)) X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq673 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq606
       grind)
    | exact superpose eq606 eq41
    | exact resolve eq41 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq606
  have eq674 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq673
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq673
    | exact resolve eq673 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq676 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq674
    | exact resolve eq674 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq684 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq676 eq608
    | exact resolve eq608 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq684
       have r₂ := eq27
       grind)
    | exact resolve eq684 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq695 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq691 eq27
    | exact resolve eq27 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ y) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq691 eq176
    | exact resolve eq176 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq697 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (σ x)) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq691 eq179
    | exact resolve eq179 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq713 : x ≠ (M.op x y) ∨ x = (M.op y y) ∨ y = (k x y) := by
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
  have eq715 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq754 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (k (σ y) X0)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq696 x
       have i₂ := eq28 sF3 x
       grind)
    | exact superpose eq28 eq696
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq696 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq774 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq697 eq697
    | exact resolve eq697 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq781 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op (M.op (M.op (M.op X0 (σ x)) (σ x)) (σ x)) (M.op (M.op X0 (σ x)) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq697 eq177
    | exact resolve eq177 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq784 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq774
  have eq786 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op (σ x) (M.op (M.op X0 (σ x)) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq697 eq781
    | exact resolve eq781 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697 eq781
  have eq1330 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq691 eq715
    | (have r₁ := eq715
       have r₂ := eq691
       grind)
    | exact resolve eq715 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq1331 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1330
  have eq1332 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq676 eq1331
    | exact resolve eq1331 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331
  have eq1342 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1332 eq181
    | exact resolve eq181 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332
  have eq1356 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1342
    | exact resolve eq1342 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342
  have eq1365 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq676 eq1356
    | exact resolve eq1356 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676 eq1356
  have eq1370 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1365
       have r₂ := eq27
       grind)
    | exact resolve eq1365 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365
  have eq1375 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1370 eq29
    | exact resolve eq29 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1385 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1370 eq695
    | exact resolve eq695 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq1386 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq1385
  have eq1396 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq1375
    | exact resolve eq1375 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1375
  have eq1400 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1396
       grind)
    | exact superpose eq1396 eq18
    | exact resolve eq18 eq1396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396
  have eq1422 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1400 eq186
    | exact resolve eq186 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq1400
  have eq1453 : x = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1422 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422
  have eq1457 : x = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq1453
  have eq1467 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1457 eq38
    | exact resolve eq38 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1457
  have eq1474 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1467
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1467
    | exact resolve eq1467 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467
  have eq1477 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1370 eq1474
    | exact resolve eq1474 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370 eq1474
  have eq1480 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1477 eq754
    | (have j0 := eq754 (σ x)
       grind)
    | exact resolve eq754 eq1477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754 eq1477
  have eq1486 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq1480
  have eq1490 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq784 eq1486
    | exact resolve eq1486 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784 eq1486
  have eq1494 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq1490
    | exact resolve eq1490 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1490
  have eq1497 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq691 eq1494
    | exact resolve eq1494 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494
  have eq1498 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1497
       have r₂ := eq1386
       grind)
    | exact resolve eq1497 eq1386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497
  have eq1509 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1498 eq786
    | exact resolve eq786 eq1498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq1518 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq1509
  have eq1530 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1498 eq1518
    | exact resolve eq1518 eq1498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498 eq1518
  have eq1540 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1530
    | exact resolve eq1530 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1530
  have eq1548 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq691 eq1540
    | exact resolve eq1540 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691 eq1540
  have eq1553 : x = (M.op x y) := by
    first
    | (have r₁ := eq1548
       have r₂ := eq1386
       grind)
    | exact resolve eq1548 eq1386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386 eq1548
  have eq1558 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1553
       grind)
    | exact superpose eq1553 eq18
    | exact resolve eq18 eq1553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1559 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq1553
       grind)
    | exact superpose eq1553 eq22
    | exact resolve eq22 eq1553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1560 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq1553
       grind)
    | exact superpose eq1553 eq36
    | exact resolve eq36 eq1553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1562 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 (M.op x y)) (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq1553
       grind)
    | exact superpose eq1553 eq178
    | exact resolve eq178 eq1553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1566 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (k (M.op x y) y) := by
    first
    | (have i₁ := eq713
       have i₂ := eq1553
       grind)
    | exact superpose eq1553 eq713
    | (have r₁ := eq713
       have r₂ := eq1553
       grind)
    | exact resolve eq713 eq1553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq1567 : (M.op x y) = (M.op y y) ∨ y = (k (M.op x y) y) := by grind
  clear eq1566
  have eq1570 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1559 eq20
    | exact resolve eq20 eq1559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1822 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1562 eq1562
    | exact resolve eq1562 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1828 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = (M.op (M.op (M.op (M.op X0 (M.op x y)) (M.op x y)) (M.op x y)) (M.op (M.op X0 (M.op x y)) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1562 eq177
    | exact resolve eq177 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1831 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = (M.op (M.op x y) (M.op (M.op X0 (M.op x y)) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1562 eq1828
    | exact resolve eq1828 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562 eq1828
  have eq2429 : y = (M.op (M.op (M.op x y) (M.op x y)) y) ∨ y = (k (M.op x y) y) := by
    first
    | (have i₁ := eq175 y
       have i₂ := eq1567
       grind)
    | exact superpose eq1567 eq175
    | exact resolve eq175 eq1567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq2430 : (k (M.op x y) y) = (M.op (M.op x y) y) ∨ y = (k (M.op x y) y) := by
    first
    | (have i₁ := eq181 y
       have i₂ := eq1567
       grind)
    | exact superpose eq1567 eq181
    | exact resolve eq181 eq1567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq1567
  have eq2439 : (M.op x y) = (k (M.op x y) y) ∨ y = (k (M.op x y) y) := by
    first
    | exact superpose eq1558 eq2430
    | exact resolve eq2430 eq1558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2430
  have eq2440 : y = (M.op (M.op x y) y) ∨ y = (k (M.op x y) y) := by
    first
    | exact superpose eq1822 eq2429
    | exact resolve eq2429 eq1822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2429
  have eq2442 : y = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1558 eq2440
    | exact resolve eq2440 eq1558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2440
  have eq2513 : y ≠ (M.op x y) ∨ y = (k (M.op x y) y) := by grind
  clear eq2439
  have eq2518 : y = (k (M.op x y) y) := by
    first
    | (have r₁ := eq2513
       have r₂ := eq2442
       grind)
    | exact resolve eq2513 eq2442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2442 eq2513
  have eq2527 : (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq2518 eq1560
    | exact resolve eq1560 eq2518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1560 eq2518
  have eq2536 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq2527
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2527
    | exact resolve eq2527 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2527
  have eq2543 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2536 eq608
    | exact resolve eq608 eq2536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq2550 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2536 eq647
    | (have j0 := eq647 (σ x) (σ y)
       grind)
    | exact resolve eq647 eq2536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2536
  have eq2551 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2550
    | exact resolve eq2550 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2550
  have eq2564 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2543 eq187
    | exact resolve eq187 eq2543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq2573 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2564
    | exact resolve eq2564 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2564
  have eq2577 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2543 eq2573
    | exact resolve eq2573 eq2543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2543 eq2573
  have eq2612 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2577 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq2577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2577
  have eq2617 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2612
       have r₂ := eq2551
       grind)
    | exact resolve eq2612 eq2551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2612
  have eq2628 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2617 eq108
    | exact resolve eq108 eq2617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq2617
  have eq2637 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq2628
    | exact resolve eq2628 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2628
  have eq2641 : (M.op x y) = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2637
       have i₂ := eq1553
       grind)
    | exact superpose eq1553 eq2637
    | exact resolve eq2637 eq1553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553 eq2637
  have eq2654 : ∀ X0 : G, y = (M.op (M.op (M.op X0 y) (M.op x y)) y) ∨ y = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2641 eq613
    | (have j0 := eq613 y (M.op x y) x
       grind)
    | exact resolve eq613 eq2641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq2655 : y ≠ (M.op x y) ∨ y = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2641 eq647
    | (have j0 := eq647 y (M.op x y)
       grind)
    | exact resolve eq647 eq2641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647 eq2641
  have eq8121 : y = (M.op (M.op (M.op x y) (M.op x y)) y) ∨ y = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1558 eq2654
    | (have j0 := eq2654 x
       grind)
    | exact resolve eq2654 eq1558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2654
  have eq8146 : y = (M.op (M.op x y) y) ∨ y = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1822 eq8121
    | exact resolve eq8121 eq1822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1822 eq8121
  have eq8156 : y = (M.op x y) ∨ y = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1558 eq8146
    | exact resolve eq8146 eq1558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8146
  have eq8165 : y = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8156
       have r₂ := eq2655
       grind)
    | exact resolve eq8156 eq2655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2655 eq8156
  have eq8182 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op y (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8165 eq1831
    | exact resolve eq1831 eq8165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1831
  have eq8204 : y = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8165 eq8182
    | exact resolve eq8182 eq8165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8165 eq8182
  have eq8210 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1558 eq8204
    | exact resolve eq8204 eq1558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1558 eq8204
  have eq8214 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8210 eq27
    | exact resolve eq27 eq8210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8210
  have eq8227 : y = (M.op x y) := by
    first
    | (have r₁ := eq8214
       have r₂ := eq1570
       grind)
    | exact resolve eq8214 eq1570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8214
  have eq8231 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq8227
       grind)
    | exact superpose eq8227 eq24
    | exact resolve eq24 eq8227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq8227
  have eq8259 : (σ x) = (σ y) := by
    first
    | exact superpose eq1559 eq8231
    | exact resolve eq8231 eq1559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1559 eq8231
  have eq8311 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8259 eq2551
    | (have r₁ := eq2551
       have r₂ := eq8259
       grind)
    | exact resolve eq2551 eq8259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2551 eq8259
  have eq8334 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8311
  have eq8415 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq8334 eq27
    | exact resolve eq27 eq8334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq8334
  have eq8429 : False := by grind
  exact eq8429

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyx_y_pyx_y_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
       have i₂ := eq34 (τ X0)
       grind)
    | exact superpose eq34 eq18
    | exact resolve eq18 eq34
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
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq83
    | exact resolve eq83 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq83
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
  have eq107 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq144 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq16
    | (have j1 := eq67 y x
       grind)
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq171 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq9
    | exact resolve eq9 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq107 (σ X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq107
    | exact resolve eq107 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq295 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq214 X0
       grind)
    | exact superpose eq214 eq9
    | exact resolve eq9 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq657 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq144
       have i₂ := eq56 y x
       grind)
    | exact superpose eq56 eq144
    | (have j1 := eq56 (σ y) (σ x)
       grind)
    | exact resolve eq144 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq658 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq657
  have eq678 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op (τ X0) (τ X0))) X1) X0) X1) = X1 := by
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
  clear eq295
  have eq696 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq678 X0 X1
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq678
    | exact resolve eq678 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq678
  have eq717 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq696 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq696
    | exact resolve eq696 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq718 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq696 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq171 X0 (σ X0)
       grind)
    | exact superpose eq171 eq696
    | exact resolve eq696 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq888 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq717 x y
       have i₂ := eq658
       grind)
    | exact superpose eq658 eq717
    | exact resolve eq717 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq2645 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq717 (σ x) (σ y)
       have i₂ := eq888
       grind)
    | exact superpose eq888 eq717
    | exact resolve eq717 eq888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq2650 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2645
       have i₂ := eq95 x
       grind)
    | exact superpose eq95 eq2645
    | exact resolve eq2645 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq2645
  have eq2987 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2650
       grind)
    | exact superpose eq2650 eq10
    | exact resolve eq10 eq2650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2650
  have eq3032 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2987
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2987
    | exact resolve eq2987 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2987
  have eq3033 : x = (M.op x x) := by grind
  clear eq3032
  have eq3212 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq696 x X0
       have i₂ := eq3033
       grind)
    | exact superpose eq3033 eq696
    | exact resolve eq696 eq3033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq3216 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq9 x x X0
       have i₂ := eq3033
       grind)
    | exact superpose eq3033 eq9
    | exact resolve eq9 eq3033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3272 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq3216 X0
       have i₂ := eq717 x X0
       grind)
    | exact superpose eq717 eq3216
    | exact resolve eq3216 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717 eq3216
  have eq3609 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3212 X0
       have i₂ := eq3272 X0
       grind)
    | exact superpose eq3272 eq3212
    | exact resolve eq3212 eq3272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3212
  have eq3708 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq3272 X0
       have i₂ := eq3609 X0
       grind)
    | exact superpose eq3609 eq3272
    | exact resolve eq3272 eq3609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3272
  have eq3866 : ∀ X0 : G, x ≠ (M.op x x) ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq3708 X0
       grind)
    | exact superpose eq3708 eq12
    | (have j0 := eq12 X0 x
       grind)
    | exact resolve eq12 eq3708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4044 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq3866 X0
       grind)
    | (have r₁ := eq3866 X0
       have r₂ := eq3033
       grind)
    | exact resolve eq3866 eq3033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3033 eq3866
  have eq4093 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq4044 X0
       have i₂ := eq3609 X0
       grind)
    | exact superpose eq3609 eq4044
    | exact resolve eq4044 eq3609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4044
  have eq4157 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq144
       have i₂ := eq4093 y
       grind)
    | exact superpose eq4093 eq144
    | exact resolve eq144 eq4093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq4093
  have eq4158 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4157
       have i₂ := eq3609 y
       grind)
    | exact superpose eq3609 eq4157
    | exact resolve eq4157 eq3609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4157
  have eq4159 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4158
  have eq6815 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4159
       grind)
    | exact superpose eq4159 eq16
    | exact resolve eq16 eq4159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6822 : (σ y) = (M.op (M.op (σ x) (σ (M.op x x))) (σ y)) := by
    first
    | (have i₁ := eq171 x (σ y)
       have i₂ := eq4159
       grind)
    | exact superpose eq4159 eq171
    | exact resolve eq171 eq4159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq6912 : (σ y) = (M.op (σ (M.op x x)) (σ y)) := by
    first
    | (have i₁ := eq6822
       have i₂ := eq718 x
       grind)
    | exact superpose eq718 eq6822
    | exact resolve eq6822 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718 eq6822
  have eq6917 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq6815
       have i₂ := eq3609 y
       grind)
    | exact superpose eq3609 eq6815
    | exact resolve eq6815 eq3609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3609 eq6815
  have eq6936 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6912
       have i₂ := eq3708 x
       grind)
    | exact superpose eq3708 eq6912
    | exact resolve eq6912 eq3708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3708 eq6912
  have eq6954 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq6936
       have i₂ := eq4159
       grind)
    | exact superpose eq4159 eq6936
    | exact resolve eq6936 eq4159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4159 eq6936
  have eq7069 : False := by grind
  exact eq7069

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_x_pyx_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq50 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
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
  have eq71 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq44
    | exact resolve eq44 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq72 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq68 sF2
       grind)
    | exact superpose eq68 eq50
    | exact resolve eq50 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
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
  have eq74 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq68 sF2
       grind)
    | exact superpose eq68 eq71
    | exact resolve eq71 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq71
  have eq79 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op X0 X0) X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq79 y x
       grind)
    | exact superpose eq79 eq102
    | (have j1 := eq79 y x
       grind)
    | exact resolve eq102 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq111
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq111
    | exact resolve eq111 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq117
    | exact resolve eq117 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq541 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq918 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq118 eq79
    | (have j0 := eq79 (σ y) (σ x)
       grind)
    | exact resolve eq79 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq118
  have eq919 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq918
    | exact resolve eq918 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq922 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq919
       have r₂ := eq28
       grind)
    | exact resolve eq919 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq926 : (τ (σ y)) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq922 eq73
    | exact resolve eq73 eq922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq922
  have eq944 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq926
    | exact resolve eq926 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq926
  have eq945 : y = (M.op x x) := by grind
  clear eq944
  have eq947 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq945
       grind)
    | exact superpose eq945 eq74
    | exact resolve eq74 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq951 : ∀ X0 : G, x = (M.op (M.op y (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq14 x x X0
       have i₂ := eq945
       grind)
    | exact superpose eq945 eq14
    | exact resolve eq14 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq958 : x = (M.op y x) := by
    first
    | (have i₁ := eq541 x
       have i₂ := eq945
       grind)
    | exact superpose eq945 eq541
    | exact resolve eq541 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq965 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq947
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq947
    | exact resolve eq947 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq967 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq958
       grind)
    | exact superpose eq958 eq14
    | exact resolve eq14 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq1002 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ x) X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq965 eq14
    | exact resolve eq14 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1010 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq965 eq541
    | exact resolve eq541 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq1020 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1010 eq14
    | exact resolve eq14 eq1010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq1129 : x = (M.op (M.op y y) x) := by
    first
    | (have i₁ := eq951 x
       have i₂ := eq945
       grind)
    | exact superpose eq945 eq951
    | exact resolve eq951 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq951
  have eq1203 : y = (M.op x y) := by
    first
    | (have i₁ := eq967 y
       have i₂ := eq1129
       grind)
    | exact superpose eq1129 eq967
    | exact resolve eq967 eq1129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967 eq1129
  have eq1211 : y = (M.op x y) := by
    first
    | (have i₁ := eq1203
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1203
    | exact resolve eq1203 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1203
  have eq1223 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1211 eq21
    | exact resolve eq21 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1211
  have eq1250 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1223
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1223
    | exact resolve eq1223 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1223
  have eq1253 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1250 eq27
    | exact resolve eq27 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1409 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq1250 eq1002
    | exact resolve eq1002 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq1439 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq965 eq1409
    | exact resolve eq1409 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965 eq1409
  have eq1449 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq1250 eq1439
    | exact resolve eq1439 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq1474 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1250 eq1020
    | exact resolve eq1020 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020 eq1250
  have eq1553 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1449 eq1474
    | exact resolve eq1474 eq1449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449 eq1474
  have eq1561 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1253 eq1553
    | exact resolve eq1553 eq1253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253 eq1553
  have eq1562 : False := by grind
  exact eq1562

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_x_pyx_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq22
  have eq77 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq70 y x
       grind)
    | exact superpose eq70 eq76
    | (have j1 := eq70 y x
       grind)
    | exact resolve eq76 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq97
    | exact resolve eq97 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq104 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (M.op x X0) (M.op x y)) X1)) X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq420 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq428 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq420 X0
       grind)
    | exact superpose eq420 eq13
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq420 X0
       grind)
    | exact resolve eq13 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq435 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq428 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq98 eq70
    | (have j0 := eq70 (σ y) x
       grind)
    | exact resolve eq70 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq824 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq823
    | exact resolve eq823 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq827 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq824
       have r₂ := eq27
       grind)
    | exact resolve eq824 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq840 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq827 eq435
    | exact resolve eq435 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq861 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq840 eq104
    | exact resolve eq104 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq840
  have eq865 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq861
    | exact resolve eq861 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq861
  have eq868 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq70 y y
       have i₂ := eq865
       grind)
    | exact superpose eq865 eq70
    | (have j0 := eq70 y x
       grind)
    | exact resolve eq70 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq869 : y = (M.op y y) := by grind
  clear eq868
  have eq888 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq869
       grind)
    | exact superpose eq869 eq14
    | exact resolve eq14 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq889 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq869
       grind)
    | exact superpose eq869 eq14
    | exact resolve eq14 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq898 : y = (k y y) := by
    first
    | (have i₁ := eq435 y
       have i₂ := eq869
       grind)
    | exact superpose eq869 eq435
    | exact resolve eq435 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435 eq869
  have eq904 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq898
       grind)
    | exact superpose eq898 eq77
    | exact resolve eq77 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq898
  have eq908 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq904
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq904
    | exact resolve eq904 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq926 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq908 eq70
    | (have j0 := eq70 (σ y) x
       grind)
    | exact resolve eq70 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq908
  have eq927 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq926
  have eq932 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq927 eq14
    | exact resolve eq14 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq977 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq889 (M.op y X0)
       have i₂ := eq888 X0
       grind)
    | exact superpose eq888 eq889
    | exact resolve eq889 eq888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1125 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq888 X0
       have i₂ := eq977 X0
       grind)
    | exact superpose eq977 eq888
    | exact resolve eq888 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888 eq977
  have eq1153 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq889 X0
       have i₂ := eq1125 X0
       grind)
    | exact superpose eq1125 eq889
    | exact resolve eq889 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq1187 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1125 X0
       have i₂ := eq1153 X0
       grind)
    | exact superpose eq1153 eq1125
    | exact resolve eq1125 eq1153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq1195 : ∀ X0 X1 : G, (M.op (M.op (M.op y X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 y X0
       have i₂ := eq1153 X0
       grind)
    | exact superpose eq1153 eq14
    | exact resolve eq14 eq1153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1222 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1195 X0 X1
       have i₂ := eq1153 X1
       grind)
    | exact superpose eq1153 eq1195
    | exact resolve eq1195 eq1153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq1272 : y = (M.op x y) := by
    first
    | (have i₁ := eq1187 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1187
    | (have j0 := eq1187 x
       grind)
    | exact resolve eq1187 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1357 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1272 eq20
    | exact resolve eq20 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1399 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1357
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1357
    | exact resolve eq1357 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1357
  have eq1421 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1399 eq26
    | exact resolve eq26 eq1399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq3036 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq932 X0
       have i₂ := eq1222 X0 sF3
       grind)
    | exact superpose eq1222 eq932
    | exact resolve eq932 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932 eq1222
  have eq3037 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1399 eq3036
    | exact resolve eq3036 eq1399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399 eq3036
  have eq3063 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (M.op x (σ (M.op x y))) (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3037 eq227
    | exact resolve eq227 eq3037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq3037
  have eq3072 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (M.op x (σ (M.op x y))) y) X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1272 eq3063
    | exact resolve eq3063 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272 eq3063
  have eq3079 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op y X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq3072 X0
       have i₂ := eq1187 (M.op x sF1)
       grind)
    | exact superpose eq1187 eq3072
    | exact resolve eq3072 eq1187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187 eq3072
  have eq3081 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq3079 X0
       have i₂ := eq1153 X0
       grind)
    | exact superpose eq1153 eq3079
    | exact resolve eq3079 eq1153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153 eq3079
  have eq3140 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3081 eq1421
    | exact resolve eq1421 eq3081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421 eq3081
  have eq3161 : False := by grind
  exact eq3161

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_y_pyx_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq36
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq76
       have i₂ := eq70 y x
       grind)
    | exact superpose eq70 eq76
    | (have j1 := eq70 x x
       grind)
    | exact resolve eq76 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq97
    | exact resolve eq97 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq420 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq428 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq420 X0
       grind)
    | exact superpose eq420 eq13
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq420 X0
       grind)
    | exact resolve eq13 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq435 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq428 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq98 eq70
    | (have j0 := eq70 x (σ x)
       grind)
    | exact resolve eq70 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq824 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq823
    | exact resolve eq823 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq827 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq824
       have r₂ := eq27
       grind)
    | exact resolve eq824 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq844 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq827 eq435
    | exact resolve eq435 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq865 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq844 eq49
    | exact resolve eq49 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq844
  have eq869 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq865
    | exact resolve eq865 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq865
  have eq872 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq70 x x
       have i₂ := eq869
       grind)
    | exact superpose eq869 eq70
    | (have j0 := eq70 x x
       grind)
    | exact resolve eq70 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq873 : x = (M.op x x) := by grind
  clear eq872
  have eq895 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq873
       grind)
    | exact superpose eq873 eq53
    | exact resolve eq53 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq896 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq873
       grind)
    | exact superpose eq873 eq50
    | exact resolve eq50 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq898 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq14 x x X0
       have i₂ := eq873
       grind)
    | exact superpose eq873 eq14
    | exact resolve eq14 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq899 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq873
       grind)
    | exact superpose eq873 eq14
    | exact resolve eq14 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq908 : x = (k x x) := by
    first
    | (have i₁ := eq435 x
       have i₂ := eq873
       grind)
    | exact superpose eq873 eq435
    | exact resolve eq435 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435 eq873
  have eq914 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq908
       grind)
    | exact superpose eq908 eq43
    | exact resolve eq43 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq908
  have eq918 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq914
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq914
    | exact resolve eq914 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq914
  have eq937 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq918 eq70
    | (have j0 := eq70 x (σ x)
       grind)
    | exact resolve eq70 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq918
  have eq938 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq937
  have eq945 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq938 eq51
    | exact resolve eq51 eq938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq938
  have eq1100 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq899 (M.op x X0)
       have i₂ := eq898 X0
       grind)
    | exact superpose eq898 eq899
    | exact resolve eq899 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1104 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq895 eq899
    | exact resolve eq899 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1118 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1104 eq895
    | exact resolve eq895 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895 eq1104
  have eq1159 : y = (M.op x y) := by
    first
    | exact superpose eq1118 eq896
    | exact resolve eq896 eq1118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896 eq1118
  have eq1173 : y = (M.op x y) := by
    first
    | (have i₁ := eq1159
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1159
    | exact resolve eq1159 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1159
  have eq1174 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1173 eq20
    | exact resolve eq20 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1173
  have eq1214 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1174
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1174
    | exact resolve eq1174 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1174
  have eq1216 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1214 eq26
    | exact resolve eq26 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1235 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq1214 eq945
    | exact resolve eq945 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq1214
  have eq1518 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq898 X0
       have i₂ := eq1100 X0
       grind)
    | exact superpose eq1100 eq898
    | exact resolve eq898 eq1100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898 eq1100
  have eq1734 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq899 X0
       have i₂ := eq1518 X0
       grind)
    | exact superpose eq1518 eq899
    | exact resolve eq899 eq1518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899 eq1518
  have eq1797 : ∀ X0 X1 : G, (M.op (M.op (M.op x X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 x X0
       have i₂ := eq1734 X0
       grind)
    | exact superpose eq1734 eq14
    | exact resolve eq14 eq1734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1827 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1797 X0 X1
       have i₂ := eq1734 X1
       grind)
    | exact superpose eq1734 eq1797
    | exact resolve eq1797 eq1734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734 eq1797
  have eq2216 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq1827
    | (have j0 := eq1827 (σ y) (σ x)
       grind)
    | exact resolve eq1827 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1827
  have eq2278 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2216 eq1235
    | exact resolve eq1235 eq2216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235 eq2216
  have eq2298 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1216 eq2278
    | exact resolve eq2278 eq1216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216 eq2278
  have eq2300 : False := by grind
  exact eq2300

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_y_pyx_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq36
  have eq83 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq83 y x
       grind)
    | exact superpose eq83 eq75
    | (have j1 := eq83 x x
       grind)
    | exact resolve eq75 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
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
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq420 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq428 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq420 X0
       grind)
    | exact superpose eq420 eq13
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq420 X0
       grind)
    | exact resolve eq13 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq435 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq428 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq113 eq83
    | (have j0 := eq83 x (σ x)
       grind)
    | exact resolve eq83 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq824 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq823
    | exact resolve eq823 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq827 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq824
       have r₂ := eq27
       grind)
    | exact resolve eq824 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq844 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq827 eq435
    | exact resolve eq435 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq865 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq844 eq49
    | exact resolve eq49 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq844
  have eq869 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq865
    | exact resolve eq865 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq865
  have eq872 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq83 x x
       have i₂ := eq869
       grind)
    | exact superpose eq869 eq83
    | (have j0 := eq83 x x
       grind)
    | exact resolve eq83 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq873 : x = (M.op x x) := by grind
  clear eq872
  have eq895 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq873
       grind)
    | exact superpose eq873 eq53
    | exact resolve eq53 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq896 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq873
       grind)
    | exact superpose eq873 eq50
    | exact resolve eq50 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq898 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq14 x x X0
       have i₂ := eq873
       grind)
    | exact superpose eq873 eq14
    | exact resolve eq14 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq899 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq873
       grind)
    | exact superpose eq873 eq14
    | exact resolve eq14 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq908 : x = (k x x) := by
    first
    | (have i₁ := eq435 x
       have i₂ := eq873
       grind)
    | exact superpose eq873 eq435
    | exact resolve eq435 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435 eq873
  have eq914 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq908
       grind)
    | exact superpose eq908 eq43
    | exact resolve eq43 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq908
  have eq918 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq914
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq914
    | exact resolve eq914 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq914
  have eq937 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq918 eq83
    | (have j0 := eq83 x (σ x)
       grind)
    | exact resolve eq83 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq918
  have eq938 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq937
  have eq945 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq938 eq51
    | exact resolve eq51 eq938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq938
  have eq1100 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq899 (M.op x X0)
       have i₂ := eq898 X0
       grind)
    | exact superpose eq898 eq899
    | exact resolve eq899 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1104 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq895 eq899
    | exact resolve eq899 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1118 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1104 eq895
    | exact resolve eq895 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895 eq1104
  have eq1159 : y = (M.op x y) := by
    first
    | exact superpose eq1118 eq896
    | exact resolve eq896 eq1118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896 eq1118
  have eq1173 : y = (M.op x y) := by
    first
    | (have i₁ := eq1159
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1159
    | exact resolve eq1159 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1159
  have eq1174 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1173 eq20
    | exact resolve eq20 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1173
  have eq1214 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1174
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1174
    | exact resolve eq1174 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1174
  have eq1216 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1214 eq26
    | exact resolve eq26 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1235 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq1214 eq945
    | exact resolve eq945 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq1214
  have eq1518 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq898 X0
       have i₂ := eq1100 X0
       grind)
    | exact superpose eq1100 eq898
    | exact resolve eq898 eq1100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898 eq1100
  have eq1734 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq899 X0
       have i₂ := eq1518 X0
       grind)
    | exact superpose eq1518 eq899
    | exact resolve eq899 eq1518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899 eq1518
  have eq1797 : ∀ X0 X1 : G, (M.op (M.op (M.op x X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 x X0
       have i₂ := eq1734 X0
       grind)
    | exact superpose eq1734 eq14
    | exact resolve eq14 eq1734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1827 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1797 X0 X1
       have i₂ := eq1734 X1
       grind)
    | exact superpose eq1734 eq1797
    | exact resolve eq1797 eq1734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734 eq1797
  have eq2216 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq1827
    | (have j0 := eq1827 (σ y) (σ x)
       grind)
    | exact resolve eq1827 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1827
  have eq2278 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2216 eq1235
    | exact resolve eq1235 eq2216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235 eq2216
  have eq2298 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1216 eq2278
    | exact resolve eq2278 eq1216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216 eq2278
  have eq2300 : False := by grind
  exact eq2300
