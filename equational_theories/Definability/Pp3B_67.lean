import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_pxx_pyx_Equation422 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq62 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X0)) X0)) := by
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
  have eq264 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq264 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq264
    | (have j0 := eq264 (σ X0) (σ X1)
       grind)
    | exact resolve eq264 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq264 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq264
    | (have j0 := eq264 (τ X0) (τ X1)
       grind)
    | exact resolve eq264 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq401 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq265 X1 X0
       have i₂ := eq264 X1 X0
       grind)
    | exact superpose eq264 eq265
    | (have j0 := eq265 X1 X0
       have j1 := eq264 (σ X1) (σ X0)
       grind)
    | exact resolve eq265 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq537 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq266 X0 X0
       grind)
    | exact superpose eq266 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq266 X0 X0
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq266 X0 X0
       grind)
    | exact resolve eq12 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X1 X0)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq266 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq542 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq537 X0 X1
       have j1 := eq12 X1 (τ X0)
       grind)
    | (have r₁ := eq537 X0 X1
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq537 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq549 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq540 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq540
    | (have j0 := eq540 (σ X1) (σ X0)
       grind)
    | exact resolve eq540 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq559 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 X1) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq549 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq549
    | (have j0 := eq549 X0 X1
       grind)
    | exact resolve eq549 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq561 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq559 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq559
    | (have j0 := eq559 X0 X1
       grind)
    | exact resolve eq559 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq562 : ∀ X0 X1 : G, (M.op (τ (σ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq561 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq561
    | (have j0 := eq561 X0 X1
       grind)
    | exact resolve eq561 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq563 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq562 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq562
    | (have j0 := eq562 X0 X1
       grind)
    | exact resolve eq562 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq565 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq563 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq563
    | (have j0 := eq563 (σ X0) (σ X1)
       grind)
    | exact resolve eq563 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq620 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq542 (σ X0) X1
       have i₂ := eq28 X0 (σ X0)
       grind)
    | exact superpose eq28 eq542
    | (have j0 := eq542 (σ X0) X1
       grind)
    | exact resolve eq542 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq621 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq620 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq620
    | (have j0 := eq620 X0 X1
       grind)
    | exact resolve eq620 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq624 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq621 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq621
    | (have j0 := eq621 X0 X1
       grind)
    | exact resolve eq621 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq629 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq624 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq624
    | (have j0 := eq624 (σ X0) X1
       grind)
    | exact resolve eq624 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq656 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X3 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 (M.op X0 (M.op X1 (M.op X2 X0))) X1 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq4923 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq401 x y
       grind)
    | exact superpose eq401 eq16
    | (have j1 := eq401 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq401 x y
       grind)
    | exact resolve eq16 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq4941 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4923
  have eq4962 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4941
       grind)
    | exact superpose eq4941 eq16
    | exact resolve eq16 eq4941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4964 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq4941
       grind)
    | exact superpose eq4941 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq4941
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq4941
       grind)
    | exact resolve eq13 eq4941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4969 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op X0 (M.op X1 (σ y)))))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq656 (σ y) (σ x) x x
       have i₂ := eq4941
       grind)
    | exact superpose eq4941 eq656
    | exact resolve eq656 eq4941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4941
  have eq4971 : (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4964
  have eq4973 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4969 x x
       have i₂ := eq9 (σ y) x x
       grind)
    | exact superpose eq9 eq4969
    | exact resolve eq4969 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4969
  have eq4974 : (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4971
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4971
    | exact resolve eq4971 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4971
  have eq4976 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq264 eq4974
    | (have j1 := eq264 (σ x) (σ x)
       grind)
    | exact resolve eq4974 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq4974
  have eq65699 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4973 eq4976
    | exact resolve eq4976 eq4973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4973 eq4976
  have eq65700 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq65699
       have r₂ := eq4962
       grind)
    | exact resolve eq65699 eq4962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4962 eq65699
  have eq65702 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq65700
       grind)
    | exact superpose eq65700 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq65700
       grind)
    | exact resolve eq12 eq65700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65732 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq65702 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65702
  have eq65736 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq65732 (σ X0)
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq65732
    | exact resolve eq65732 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65769 : ∀ X0 : G, (τ (σ x)) ≠ (τ (M.op (σ x) (σ x))) ∨ (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq542 (σ x) X0
       have i₂ := eq65732 (σ x)
       grind)
    | exact superpose eq65732 eq542
    | (have j0 := eq542 (σ x) X0
       grind)
    | exact resolve eq542 eq65732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542 eq65732
  have eq65883 : ∀ X0 : G, x ≠ (τ (M.op (σ x) (σ x))) ∨ (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq65769 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq65769
    | (have j0 := eq65769 X0
       grind)
    | exact resolve eq65769 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65769
  have eq65894 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x ≠ (τ (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq65883 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq65883
    | exact resolve eq65883 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65883
  have eq65896 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x ≠ (τ (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq65700 eq65894
    | (have j0 := eq65894 X0
       grind)
    | exact resolve eq65894 eq65700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65700 eq65894
  have eq65898 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq65896 X0
       grind)
    | (have r₁ := eq65896 X0
       have r₂ := eq10 x
       grind)
    | exact resolve eq65896 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65896
  have eq66153 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq65898 eq65736
    | exact resolve eq65736 eq65898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65736 eq65898
  have eq66210 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66153 y
       grind)
    | exact superpose eq66153 eq16
    | (have r₁ := eq16
       have r₂ := eq66153 y
       grind)
    | exact resolve eq16 eq66153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66153
  have eq66348 : y = (M.op x y) := by grind
  clear eq66210
  have eq66500 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66348
       grind)
    | exact superpose eq66348 eq16
    | exact resolve eq16 eq66348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66502 : y ≠ y ∨ x = (M.op x x) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq66348
       grind)
    | exact superpose eq66348 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq66348
       grind)
    | exact resolve eq13 eq66348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66507 : ∀ X0 X1 : G, y = (M.op y (M.op y (M.op y (M.op X0 (M.op X1 y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq656 y x x x
       have i₂ := eq66348
       grind)
    | exact superpose eq66348 eq656
    | exact resolve eq656 eq66348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq66532 : x = (M.op x x) ∨ (k y x) = (M.op y y) := by grind
  clear eq66502
  have eq66535 : y = (M.op y y) := by
    first
    | (have i₁ := eq66507 x x
       have i₂ := eq9 y x x
       grind)
    | exact superpose eq9 eq66507
    | exact resolve eq66507 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66507
  have eq68008 : y = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq66532
       have i₂ := eq66535
       grind)
    | exact superpose eq66535 eq66532
    | exact resolve eq66532 eq66535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66532 eq66535
  have eq68015 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq565 y x
       have i₂ := eq68008
       grind)
    | exact superpose eq68008 eq565
    | (have j0 := eq565 y x
       grind)
    | exact resolve eq565 eq68008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565 eq68008
  have eq68018 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq68015
  have eq68025 : x = (M.op x x) := by
    first
    | (have r₁ := eq68018
       have r₂ := eq66500
       grind)
    | exact resolve eq68018 eq66500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68018
  have eq68027 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq68025
       grind)
    | exact superpose eq68025 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq68025
       grind)
    | exact resolve eq12 eq68025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68058 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq68027 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68027
  have eq68063 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq629 x X0
       have i₂ := eq68058 x
       grind)
    | exact superpose eq68058 eq629
    | (have j0 := eq629 x X0
       grind)
    | exact resolve eq629 eq68058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq68108 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq68063 X0
       have i₂ := eq68025
       grind)
    | exact superpose eq68025 eq68063
    | (have j0 := eq68063 X0
       grind)
    | exact resolve eq68063 eq68025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68025 eq68063
  have eq68109 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq68108 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68108
  have eq68326 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq68109 (σ X0)
       grind)
    | exact superpose eq68109 eq15
    | exact resolve eq15 eq68109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68109
  have eq68414 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq68326 X0
       have i₂ := eq68058 X0
       grind)
    | exact superpose eq68058 eq68326
    | exact resolve eq68326 eq68058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68058 eq68326
  have eq68874 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq66500
       have i₂ := eq68414 y
       grind)
    | exact superpose eq68414 eq66500
    | exact resolve eq66500 eq68414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66500 eq68414
  have eq68948 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq68874
       have i₂ := eq66348
       grind)
    | exact superpose eq66348 eq68874
    | exact resolve eq68874 eq66348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66348 eq68874
  have eq68949 : False := by grind
  exact eq68949

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_pxy_pyx_Equation422 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq62 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X0)) X0)) := by
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
  have eq264 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq264 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq264
    | (have j0 := eq264 (σ X0) (σ X1)
       grind)
    | exact resolve eq264 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq264 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq264
    | (have j0 := eq264 (τ X0) (τ X1)
       grind)
    | exact resolve eq264 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq401 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq265 X1 X0
       have i₂ := eq264 X1 X0
       grind)
    | exact superpose eq264 eq265
    | (have j0 := eq265 X1 X0
       have j1 := eq264 (σ X1) (σ X0)
       grind)
    | exact resolve eq265 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq265 X1 X0
       grind)
    | exact superpose eq265 eq10
    | (have j1 := eq265 X1 X0
       grind)
    | exact resolve eq10 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq537 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq266 X0 X0
       grind)
    | exact superpose eq266 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq266 X0 X0
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq266 X0 X0
       grind)
    | exact resolve eq12 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq542 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq537 X0 X1
       have j1 := eq12 X1 (τ X0)
       grind)
    | (have r₁ := eq537 X0 X1
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq537 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq620 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq542 (σ X0) X1
       have i₂ := eq28 X0 (σ X0)
       grind)
    | exact superpose eq28 eq542
    | (have j0 := eq542 (σ X0) X1
       grind)
    | exact resolve eq542 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq621 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq620 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq620
    | (have j0 := eq620 X0 X1
       grind)
    | exact resolve eq620 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq624 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq621 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq621
    | (have j0 := eq621 X0 X1
       grind)
    | exact resolve eq621 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq629 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq624 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq624
    | (have j0 := eq624 (σ X0) X1
       grind)
    | exact resolve eq624 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq656 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X3 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 (M.op X0 (M.op X1 (M.op X2 X0))) X1 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq666 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op (M.op X0 (M.op X1 X2)) X2) (M.op X3 (M.op X4 (M.op (M.op X0 (M.op X1 X2)) X2)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq656 (M.op (M.op X1 (M.op X2 X0)) X0) (M.op X1 (M.op X2 X0)) X2 X3
       have i₂ := eq62 X0 X1 X2
       grind)
    | exact superpose eq62 eq656
    | exact resolve eq656 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4923 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq401 x y
       grind)
    | exact superpose eq401 eq16
    | (have j1 := eq401 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq401 x y
       grind)
    | exact resolve eq16 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq4941 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4923
  have eq4964 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq4941
       grind)
    | exact superpose eq4941 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq4941
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq4941
       grind)
    | exact resolve eq13 eq4941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4969 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op X0 (M.op X1 (σ y)))))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq656 (σ y) (σ x) x x
       have i₂ := eq4941
       grind)
    | exact superpose eq4941 eq656
    | exact resolve eq656 eq4941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4941
  have eq4971 : (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq4964
  have eq4973 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4969 x x
       have i₂ := eq9 (σ y) x x
       grind)
    | exact superpose eq9 eq4969
    | exact resolve eq4969 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4969
  have eq4974 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4971
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4971
    | exact resolve eq4971 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4971
  have eq4976 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq264 eq4974
    | (have j1 := eq264 (σ x) (σ x)
       grind)
    | exact resolve eq4974 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq4974
  have eq4978 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq4973
       grind)
    | exact superpose eq4973 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq4973
       grind)
    | exact resolve eq12 eq4973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4985 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4978 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4978
  have eq4988 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4985 (σ X0)
       have i₂ := eq15 X0 y
       grind)
    | exact superpose eq15 eq4985
    | exact resolve eq4985 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4995 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22 X0 y
       have i₂ := eq4985 X0
       grind)
    | exact superpose eq4985 eq22
    | exact resolve eq22 eq4985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5017 : ∀ X0 : G, (τ (σ y)) ≠ (τ (M.op (σ y) (σ y))) ∨ (k X0 (τ (σ y))) = (M.op (τ (σ y)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq542 (σ y) X0
       have i₂ := eq4985 (σ y)
       grind)
    | exact superpose eq4985 eq542
    | (have j0 := eq542 (σ y) X0
       grind)
    | exact resolve eq542 eq4985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4985
  have eq5096 : ∀ X0 : G, y ≠ (τ (M.op (σ y) (σ y))) ∨ (k X0 (τ (σ y))) = (M.op (τ (σ y)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5017 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5017
    | (have j0 := eq5017 X0
       grind)
    | exact resolve eq5017 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5017
  have eq5106 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ y ≠ (τ (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5096 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5096
    | exact resolve eq5096 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5096
  have eq5108 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ y ≠ (τ (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4973 eq5106
    | (have j0 := eq5106 X0
       grind)
    | exact resolve eq5106 eq4973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5106
  have eq5110 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq5108 X0
       grind)
    | (have r₁ := eq5108 X0
       have r₂ := eq10 y
       grind)
    | exact resolve eq5108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5108
  have eq5251 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (M.op y X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5110 eq4988
    | exact resolve eq4988 eq5110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4988
  have eq5252 : ∀ X0 : G, (τ (M.op (σ y) X0)) = (M.op y (τ X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5110 eq4995
    | exact resolve eq4995 eq5110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4995 eq5110
  have eq5266 : (σ y) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4973
       have i₂ := eq5251 y
       grind)
    | exact superpose eq5251 eq4973
    | exact resolve eq4973 eq5251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4973
  have eq5273 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (M.op X1 (σ (M.op y X0))))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ y)
       have i₂ := eq5251 X0
       grind)
    | exact superpose eq5251 eq9
    | exact resolve eq9 eq5251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5251
  have eq5283 : (σ y) = (σ (M.op y y)) ∨ y = (M.op x y) := by grind
  clear eq5266
  have eq5301 : (τ (σ y)) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq5283
       grind)
    | exact superpose eq5283 eq10
    | exact resolve eq10 eq5283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5283
  have eq5445 : y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5301
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5301
    | exact resolve eq5301 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5301
  have eq5484 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op X0 y) (M.op (M.op X0 y) (M.op y (M.op X1 y)))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq656 y X0 X1 y
       have i₂ := eq5445
       grind)
    | exact superpose eq5445 eq656
    | exact resolve eq656 eq5445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5445
  have eq23759 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op X0 y) (M.op X0 y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 y) (M.op X0 y) y
       have i₂ := eq5484 X0 X0
       grind)
    | exact superpose eq5484 eq9
    | exact resolve eq9 eq5484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5484
  have eq23834 : ∀ X0 X1 : G, (M.op X0 y) ≠ (M.op X0 y) ∨ (k X1 (M.op X0 y)) = (M.op (M.op X0 y) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 y)
       have i₂ := eq23759 X0
       grind)
    | exact superpose eq23759 eq12
    | (have j0 := eq12 X1 (M.op X0 y)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 y)
       have r₂ := eq23759 X0
       grind)
    | exact resolve eq12 eq23759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23855 : ∀ X0 X1 : G, (k X1 (M.op X0 y)) = (M.op (M.op X0 y) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq23834 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23834
  have eq23864 : ∀ X0 X1 : G, (σ (M.op X0 y)) ≠ (σ (M.op (M.op X0 y) (M.op X0 y))) ∨ (k X1 (σ (M.op X0 y))) = (M.op (σ (M.op X0 y)) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq629 (M.op X0 y) X1
       have i₂ := eq23855 X0 (M.op X0 y)
       grind)
    | exact superpose eq23855 eq629
    | (have j0 := eq629 (M.op X0 y) X1
       grind)
    | exact resolve eq629 eq23855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23929 : ∀ X0 X1 : G, (σ (M.op X0 y)) ≠ (σ (M.op X0 y)) ∨ (k X1 (σ (M.op X0 y))) = (M.op (σ (M.op X0 y)) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq23759 eq23864
    | (have j0 := eq23864 X0 X1
       grind)
    | exact resolve eq23864 eq23759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23864
  have eq23930 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 y))) = (M.op (σ (M.op X0 y)) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq23929 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23929
  have eq24138 : ∀ X0 X1 : G, (σ (k X1 (M.op X0 y))) = (M.op (σ (M.op X0 y)) (σ X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (M.op X0 y)
       have i₂ := eq23930 X0 (σ X1)
       grind)
    | exact superpose eq23930 eq15
    | exact resolve eq15 eq23930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23930
  have eq24246 : ∀ X0 X1 : G, (M.op (σ (M.op X0 y)) (σ X1)) = (σ (M.op (M.op X0 y) X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq23855 eq24138
    | exact resolve eq24138 eq23855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23855 eq24138
  have eq65376 : (τ (σ (M.op x y))) = (M.op y (τ (σ x))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5252 (σ x)
       have i₂ := eq4976
       grind)
    | exact superpose eq4976 eq5252
    | exact resolve eq5252 eq4976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4976 eq5252
  have eq65427 : (τ (σ (M.op x y))) = (M.op y (τ (σ x))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq65376
  have eq65441 : (M.op y x) = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq65427
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq65427
    | exact resolve eq65427 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65427
  have eq65456 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq65441
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq65441
    | exact resolve eq65441 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65441
  have eq65469 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq65456
  have eq65477 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq65469
       grind)
    | exact superpose eq65469 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq65469
       grind)
    | exact resolve eq12 eq65469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65507 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq65477 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65477
  have eq65511 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq65507 (σ X0)
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq65507
    | exact resolve eq65507 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65543 : ∀ X0 : G, (τ (σ x)) ≠ (τ (M.op (σ x) (σ x))) ∨ (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq542 (σ x) X0
       have i₂ := eq65507 (σ x)
       grind)
    | exact superpose eq65507 eq542
    | (have j0 := eq542 (σ x) X0
       grind)
    | exact resolve eq542 eq65507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65507
  have eq65657 : ∀ X0 : G, x ≠ (τ (M.op (σ x) (σ x))) ∨ (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq65543 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq65543
    | (have j0 := eq65543 X0
       grind)
    | exact resolve eq65543 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65543
  have eq65668 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x ≠ (τ (M.op (σ x) (σ x))) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq65657 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq65657
    | exact resolve eq65657 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65657
  have eq65670 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x ≠ (τ (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq65469 eq65668
    | (have j0 := eq65668 X0
       grind)
    | exact resolve eq65668 eq65469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65469 eq65668
  have eq65672 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq65670 X0
       grind)
    | (have r₁ := eq65670 X0
       have r₂ := eq10 x
       grind)
    | exact resolve eq65670 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65670
  have eq65927 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq65672 eq65511
    | exact resolve eq65511 eq65672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65511 eq65672
  have eq65984 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65927 y
       grind)
    | exact superpose eq65927 eq16
    | (have r₁ := eq16
       have r₂ := eq65927 y
       grind)
    | exact resolve eq16 eq65927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65927
  have eq66122 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq65984
  have eq66276 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ (M.op x y))))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5273 x X0
       have i₂ := eq66122
       grind)
    | exact superpose eq66122 eq5273
    | exact resolve eq5273 eq66122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5273
  have eq66286 : ∀ X0 : G, x = (M.op x (M.op x (M.op X0 (M.op x y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 y
       have i₂ := eq66122
       grind)
    | exact superpose eq66122 eq9
    | exact resolve eq9 eq66122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66122
  have eq66328 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ (M.op x y))))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq66276 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66276
  have eq66982 : x = (M.op x (M.op x (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq66286 (M.op x y)
       have i₂ := eq23759 x
       grind)
    | exact superpose eq23759 eq66286
    | exact resolve eq66286 eq23759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67043 : x = (M.op x (M.op x (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq66982
  have eq67044 : x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq66286 x
       have i₂ := eq67043
       grind)
    | exact superpose eq67043 eq66286
    | exact resolve eq66286 eq67043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66286 eq67043
  have eq67103 : y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq67044
  have eq67105 : y ≠ y ∨ x = (M.op x x) ∨ (k y x) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq67103
       grind)
    | exact superpose eq67103 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq67103
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq67103
       grind)
    | exact resolve eq13 eq67103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67103
  have eq67135 : y ≠ y ∨ x = (M.op x x) ∨ (k y x) = (M.op y x) := by grind
  clear eq67105
  have eq67136 : (k y x) = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq67135
  have eq75543 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (σ (M.op (M.op X0 y) (M.op x y))))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq66328 (σ (M.op X0 y))
       have i₂ := eq24246 X0 (M.op x y)
       grind)
    | exact superpose eq24246 eq66328
    | exact resolve eq66328 eq24246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24246
  have eq75620 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (σ (M.op (M.op X0 y) (M.op x y))))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq75543 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75543
  have eq109391 : (σ x) = (M.op (σ x) (M.op (σ x) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq75620 x
       have i₂ := eq23759 x
       grind)
    | exact superpose eq23759 eq75620
    | exact resolve eq75620 eq23759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23759 eq75620
  have eq109462 : (σ x) = (M.op (σ x) (M.op (σ x) (σ (M.op x y)))) ∨ y = (M.op x y) := by grind
  clear eq109391
  have eq109468 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq66328 (σ x)
       have i₂ := eq109462
       grind)
    | exact superpose eq109462 eq66328
    | exact resolve eq66328 eq109462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66328 eq109462
  have eq109533 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq109468
  have eq109564 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq109533
       grind)
    | exact superpose eq109533 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq109533
       grind)
    | exact resolve eq12 eq109533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109598 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq109564 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109564
  have eq109604 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq109598 (σ X0)
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq109598
    | exact resolve eq109598 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109643 : ∀ X0 : G, (τ (σ x)) ≠ (τ (M.op (σ x) (σ x))) ∨ (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq542 (σ x) X0
       have i₂ := eq109598 (σ x)
       grind)
    | exact superpose eq109598 eq542
    | (have j0 := eq542 (σ x) X0
       grind)
    | exact resolve eq542 eq109598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542 eq109598
  have eq109773 : ∀ X0 : G, x ≠ (τ (M.op (σ x) (σ x))) ∨ (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq109643 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq109643
    | (have j0 := eq109643 X0
       grind)
    | exact resolve eq109643 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109643
  have eq109787 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x ≠ (τ (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq109773 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq109773
    | exact resolve eq109773 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109773
  have eq109790 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x ≠ (τ (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq109533 eq109787
    | (have j0 := eq109787 X0
       grind)
    | exact resolve eq109787 eq109533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109533 eq109787
  have eq109792 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq109790 X0
       grind)
    | (have r₁ := eq109790 X0
       have r₂ := eq10 x
       grind)
    | exact resolve eq109790 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109790
  have eq110088 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq109792 eq109604
    | exact resolve eq109604 eq109792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109604 eq109792
  have eq110171 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq110088 y
       grind)
    | exact superpose eq110088 eq16
    | (have r₁ := eq16
       have r₂ := eq110088 y
       grind)
    | exact resolve eq16 eq110088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110088
  have eq110337 : y = (M.op x y) := by grind
  clear eq110171
  have eq110482 : y = (M.op x y) := by grind
  clear eq110337
  have eq110506 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq110482
       grind)
    | exact superpose eq110482 eq16
    | exact resolve eq16 eq110482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110554 : ∀ X0 X1 : G, y = (M.op y (M.op y (M.op y (M.op X0 (M.op X1 y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq656 y x x x
       have i₂ := eq110482
       grind)
    | exact superpose eq110482 eq656
    | exact resolve eq656 eq110482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110555 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op X0 y) (M.op (M.op X0 y) (M.op y (M.op X1 y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq656 y X0 X1 x
       have i₂ := eq110482
       grind)
    | exact superpose eq110482 eq656
    | exact resolve eq656 eq110482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq110587 : y = (M.op y y) := by
    first
    | (have i₁ := eq110554 x x
       have i₂ := eq9 y x x
       grind)
    | exact superpose eq9 eq110554
    | exact resolve eq110554 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110554
  have eq110656 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq110587
       grind)
    | exact superpose eq110587 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq110587
       grind)
    | exact resolve eq12 eq110587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110690 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq110656 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110656
  have eq111172 : ∀ X0 : G, (σ y) ≠ (σ (M.op y y)) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq629 y X0
       have i₂ := eq110690 y
       grind)
    | exact superpose eq110690 eq629
    | (have j0 := eq629 y X0
       grind)
    | exact resolve eq629 eq110690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111231 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq111172 X0
       have i₂ := eq110587
       grind)
    | exact superpose eq110587 eq111172
    | (have j0 := eq111172 X0
       grind)
    | exact resolve eq111172 eq110587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111172
  have eq111232 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq111231 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111231
  have eq111484 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq22 X0 y
       have i₂ := eq111232 X0
       grind)
    | exact superpose eq111232 eq22
    | exact resolve eq22 eq111232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq111523 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq111232 (σ X0)
       grind)
    | exact superpose eq111232 eq15
    | exact resolve eq15 eq111232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111232
  have eq111625 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq111523 X0
       have i₂ := eq110690 X0
       grind)
    | exact superpose eq110690 eq111523
    | exact resolve eq111523 eq110690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111523
  have eq111653 : ∀ X0 : G, (τ (M.op (σ y) X0)) = (M.op y (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq111484 X0
       have i₂ := eq110690 (τ X0)
       grind)
    | exact superpose eq110690 eq111484
    | exact resolve eq111484 eq110690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110690 eq111484
  have eq112666 : ∀ X0 X1 : G, (τ (σ y)) = (M.op y (τ (M.op (σ y) (M.op X0 (M.op X1 (σ y)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq111653 (M.op (σ y) (M.op X0 (M.op X1 (σ y))))
       have i₂ := eq9 (σ y) X0 X1
       grind)
    | exact superpose eq9 eq111653
    | exact resolve eq111653 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112794 : ∀ X0 X1 : G, (τ (σ y)) = (M.op y (M.op y (τ (M.op X0 (M.op X1 (σ y)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq112666 X0 X1
       have i₂ := eq111653 (M.op X0 (M.op X1 (σ y)))
       grind)
    | exact superpose eq111653 eq112666
    | exact resolve eq112666 eq111653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111653 eq112666
  have eq112815 : ∀ X0 X1 : G, y = (M.op y (M.op y (τ (M.op X0 (M.op X1 (σ y)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq112794 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq112794
    | exact resolve eq112794 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112794
  have eq114586 : ∀ X0 : G, y = (M.op y (M.op y (τ (M.op X0 (σ (M.op y y)))))) := by
    intro X0
    first
    | (have i₁ := eq112815 X0 (σ y)
       have i₂ := eq111625 y
       grind)
    | exact superpose eq111625 eq112815
    | exact resolve eq112815 eq111625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111625 eq112815
  have eq114681 : ∀ X0 : G, y = (M.op y (M.op y (τ (M.op X0 (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq114586 X0
       have i₂ := eq110587
       grind)
    | exact superpose eq110587 eq114586
    | exact resolve eq114586 eq110587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110587 eq114586
  have eq114698 : ∀ X0 : G, y = (M.op y (M.op y (k y X0))) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq114681 (σ X0)
       have i₂ := eq420 X0 y
       grind)
    | exact superpose eq420 eq114681
    | (have j1 := eq420 X0 y
       grind)
    | exact resolve eq114681 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420 eq114681
  have eq149143 : y = (M.op y (M.op y (M.op y x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq114698 x
       have i₂ := eq67136
       grind)
    | exact superpose eq67136 eq114698
    | (have j0 := eq114698 x
       grind)
    | exact resolve eq114698 eq67136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67136 eq114698
  have eq149247 : y = (M.op y (M.op y (M.op y x))) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq149143
       have r₂ := eq110506
       grind)
    | exact resolve eq149143 eq110506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149143
  have eq149266 : (M.op y x) = (M.op (M.op y x) (M.op (M.op y x) y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op y x) y y
       have i₂ := eq149247
       grind)
    | exact superpose eq149247 eq9
    | exact resolve eq9 eq149247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149247
  have eq311251 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op X0 (M.op X1 y)) (M.op (M.op X0 (M.op X1 y)) (M.op (M.op X0 (M.op X1 y)) y))) := by
    intro X0 X1
    first
    | (have i₁ := eq666 X0 X1 y (M.op (M.op X0 (M.op X1 y)) y) y
       have i₂ := eq110555 (M.op X0 (M.op X1 y)) (M.op X0 (M.op X1 y))
       grind)
    | exact superpose eq110555 eq666
    | exact resolve eq666 eq110555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666 eq110555
  have eq311331 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op X0 (M.op X1 y)) (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq311251 X0 X1
       have i₂ := eq62 y X0 X1
       grind)
    | exact superpose eq62 eq311251
    | exact resolve eq311251 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq311251
  have eq311338 : (M.op y x) = (M.op (M.op y x) (M.op y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq311331 (M.op y x) (M.op y x)
       have i₂ := eq149266
       grind)
    | exact superpose eq149266 eq311331
    | exact resolve eq311331 eq149266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149266 eq311331
  have eq317119 : x = (M.op x (M.op x (M.op y x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 x (M.op y x) y
       have i₂ := eq311338
       grind)
    | exact superpose eq311338 eq9
    | exact resolve eq9 eq311338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311338
  have eq317195 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 x x y
       have i₂ := eq317119
       grind)
    | exact superpose eq317119 eq9
    | exact resolve eq9 eq317119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317119
  have eq317294 : x = (M.op x x) := by grind
  clear eq317195
  have eq317299 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq317294
       grind)
    | exact superpose eq317294 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq317294
       grind)
    | exact resolve eq12 eq317294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317338 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq317299 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317299
  have eq317349 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq629 x X0
       have i₂ := eq317338 x
       grind)
    | exact superpose eq317338 eq629
    | (have j0 := eq629 x X0
       grind)
    | exact resolve eq629 eq317338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq317445 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq317349 X0
       have i₂ := eq317294
       grind)
    | exact superpose eq317294 eq317349
    | (have j0 := eq317349 X0
       grind)
    | exact resolve eq317349 eq317294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317294 eq317349
  have eq317446 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq317445 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317445
  have eq317905 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq317446 (σ X0)
       grind)
    | exact superpose eq317446 eq15
    | exact resolve eq15 eq317446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317446
  have eq318064 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq317905 X0
       have i₂ := eq317338 X0
       grind)
    | exact superpose eq317338 eq317905
    | exact resolve eq317905 eq317338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317338 eq317905
  have eq320330 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq110506
       have i₂ := eq318064 y
       grind)
    | exact superpose eq318064 eq110506
    | exact resolve eq110506 eq318064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110506 eq318064
  have eq320763 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq320330
       have i₂ := eq110482
       grind)
    | exact superpose eq110482 eq320330
    | exact resolve eq320330 eq110482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110482 eq320330
  have eq320764 : False := by grind
  exact eq320764

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation422 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq80 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq82 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 (τ X1)) ∨ (M.op X0 X0) = X0 := by
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
  have eq86 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq201 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq79 X0 X0
       grind)
    | exact superpose eq79 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq79 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq79 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq79 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq204 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq203 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq205 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq201 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq207 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq205 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq205 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq205 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq216 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq204 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq204
    | (have j0 := eq204 (τ X0)
       grind)
    | exact resolve eq204 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq204
  have eq218 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq216 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq216
    | (have j0 := eq216 X0
       grind)
    | exact resolve eq216 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq221 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq218 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq218
    | (have j0 := eq218 X0
       grind)
    | exact resolve eq218 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq227 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq221 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq221
    | (have j0 := eq221 (τ X0)
       grind)
    | exact resolve eq221 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq573 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq82
    | (have j0 := eq82 X1 X1
       grind)
    | exact resolve eq82 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq606 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq573 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq573
    | (have j0 := eq573 X0 X1
       grind)
    | exact resolve eq573 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq3636 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq80 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq3637 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq3636 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3636
  have eq3640 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3637 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3637
    | (have j0 := eq3637 X0
       grind)
    | exact resolve eq3637 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3637
  have eq3876 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3640 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3640
    | exact resolve eq3640 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3640
  have eq3920 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3876 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq3876
    | (have j0 := eq3876 X0
       grind)
    | exact resolve eq3876 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3876
  have eq3922 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq3920 X0
       grind)
    | exact superpose eq3920 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq3920 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq3920 X0
       grind)
    | exact resolve eq12 eq3920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3920
  have eq3964 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq3922 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3922
  have eq4082 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3964 X0 X1
       grind)
    | exact superpose eq3964 eq11
    | (have j1 := eq3964 X0 X1
       grind)
    | exact resolve eq11 eq3964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3964
  have eq4189 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4082 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4082
    | (have j0 := eq4082 X0 X0
       grind)
    | exact resolve eq4082 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4082
  have eq4276 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4189 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4189
  have eq4277 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4276 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4276
  have eq4500 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq207 X0 X1
       have i₂ := eq4277 X0
       grind)
    | exact superpose eq4277 eq207
    | (have j0 := eq207 X0 X1
       grind)
    | exact resolve eq207 eq4277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq4503 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq227 X0
       have i₂ := eq4277 X0
       grind)
    | exact superpose eq4277 eq227
    | (have j0 := eq227 X0
       grind)
    | exact resolve eq227 eq4277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq4539 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4277 (σ X0)
       grind)
    | exact superpose eq4277 eq15
    | exact resolve eq15 eq4277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4546 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq4277 (τ X0)
       grind)
    | exact superpose eq4277 eq33
    | exact resolve eq33 eq4277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq4600 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4546 X0
       have i₂ := eq4277 X0
       grind)
    | exact superpose eq4277 eq4546
    | exact resolve eq4546 eq4277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4546
  have eq4606 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4539 X0
       have i₂ := eq4277 X0
       grind)
    | exact superpose eq4277 eq4539
    | exact resolve eq4539 eq4277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4277 eq4539
  have eq6199 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4503 (σ X0)
       have i₂ := eq86 X0 X1
       grind)
    | exact superpose eq86 eq4503
    | (have j0 := eq4503 (σ X0)
       have j1 := eq86 X0 X1
       grind)
    | exact resolve eq4503 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq4503
  have eq6239 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq6199 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6199
  have eq6251 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6239 X0 X1
       have i₂ := eq4600 (σ X0)
       grind)
    | exact superpose eq4600 eq6239
    | (have j0 := eq6239 X0 X1
       grind)
    | exact resolve eq6239 eq4600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4600 eq6239
  have eq6260 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6251 X0 X1
       have i₂ := eq4606 X0
       grind)
    | exact superpose eq4606 eq6251
    | (have j0 := eq6251 X0 X1
       grind)
    | exact resolve eq6251 eq4606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6251
  have eq6264 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6260 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq6260
    | (have j0 := eq6260 X0 X1
       grind)
    | exact resolve eq6260 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6260
  have eq6266 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6264 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6264
    | (have j0 := eq6264 X0 X1
       grind)
    | exact resolve eq6264 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6264
  have eq10534 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) X0)
       have i₂ := eq6266 X1 X0
       grind)
    | exact superpose eq6266 eq11
    | (have j1 := eq6266 X1 X0
       grind)
    | exact resolve eq11 eq6266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6266
  have eq10608 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10534 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq10534
    | (have j0 := eq10534 X0 X1
       grind)
    | exact resolve eq10534 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq10534
  have eq10697 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq10608 (σ X1) X0
       grind)
    | exact superpose eq10608 eq15
    | (have j1 := eq10608 (σ X1) X0
       grind)
    | exact resolve eq15 eq10608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10608
  have eq24945 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10697 x y
       grind)
    | exact superpose eq10697 eq16
    | (have j1 := eq10697 x y
       grind)
    | exact resolve eq16 eq10697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25044 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq10697 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10697
  have eq25913 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24945
       have i₂ := eq606 y x
       grind)
    | exact superpose eq606 eq24945
    | (have j1 := eq606 x x
       grind)
    | (have r₁ := eq24945
       have r₂ := eq606 y x
       grind)
    | exact resolve eq24945 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24945
  have eq25914 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq25913
  have eq25915 : y = (M.op x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq25914
  have eq26163 : y ≠ y ∨ y = (k y x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq25915
       grind)
    | exact superpose eq25915 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq25915
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq25915
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq25915
       grind)
    | exact resolve eq13 eq25915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25915
  have eq26202 : y ≠ y ∨ y = (k y x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq26163
  have eq26203 : y = (k y x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq26202
  have eq26240 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25044 x y
       have i₂ := eq26203
       grind)
    | exact superpose eq26203 eq25044
    | (have j0 := eq25044 x y
       grind)
    | exact resolve eq25044 eq26203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25044 eq26203
  have eq26243 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq26240
  have eq26244 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq26243
  have eq26489 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26244
       grind)
    | exact superpose eq26244 eq16
    | exact resolve eq16 eq26244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26492 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq26244
       grind)
    | exact superpose eq26244 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq26244
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq26244
       grind)
    | exact resolve eq13 eq26244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26244
  have eq26531 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq26492
  have eq26540 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq26531
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq26531
    | exact resolve eq26531 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26531
  have eq26548 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq26540
       have i₂ := eq4606 x
       grind)
    | exact superpose eq4606 eq26540
    | exact resolve eq26540 eq4606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4606 eq26540
  have eq99747 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq606 y x
       have i₂ := eq26548
       grind)
    | exact superpose eq26548 eq606
    | (have j0 := eq606 y x
       grind)
    | exact resolve eq606 eq26548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606 eq26548
  have eq99914 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq99747
  have eq99993 : y = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq99914
       have r₂ := eq26489
       grind)
    | exact resolve eq99914 eq26489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99914
  have eq100893 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq26489
       have i₂ := eq99993
       grind)
    | exact superpose eq99993 eq26489
    | exact resolve eq26489 eq99993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26489 eq99993
  have eq100983 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq100893
  have eq100984 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq100983
  have eq101356 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq100984
       grind)
    | exact superpose eq100984 eq10
    | exact resolve eq10 eq100984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100984
  have eq101595 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq101356
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq101356
    | exact resolve eq101356 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101356
  have eq101596 : x = (M.op x x) := by grind
  clear eq101595
  have eq101614 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq101596
       grind)
    | exact superpose eq101596 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq101596
       grind)
    | exact resolve eq12 eq101596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101619 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq4500 x X0
       have i₂ := eq101596
       grind)
    | exact superpose eq101596 eq4500
    | (have j0 := eq4500 x X0
       grind)
    | exact resolve eq4500 eq101596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4500 eq101596
  have eq101728 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq101619 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101619
  have eq101733 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq101614 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101614
  have eq103826 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq101728 (σ X0)
       grind)
    | exact superpose eq101728 eq15
    | exact resolve eq15 eq101728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101728
  have eq103928 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq103826 X0
       have i₂ := eq101733 X0
       grind)
    | exact superpose eq101733 eq103826
    | exact resolve eq103826 eq101733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101733 eq103826
  have eq107575 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq103928 y
       grind)
    | exact superpose eq103928 eq16
    | (have r₁ := eq16
       have r₂ := eq103928 y
       grind)
    | exact resolve eq16 eq103928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103928
  have eq107778 : False := by grind
  exact eq107778

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyx_Equation422 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law422 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq19 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X1 X1) ≠ (k X0 X0) := by
    intro X0 X1
    grind
  clear eq18
  have eq21 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X1 X1) = (k X0 X0) := by
    intro X0 X1
    grind
  clear eq19
  have eq22 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ x = y ∨ (k y y) ≠ (k x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq20 x y
       grind)
    | exact superpose eq20 eq9
    | (have j1 := eq20 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq20 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq20 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : (k y y) ≠ (k x x) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq561
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq561
    | exact resolve eq561 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq1212 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ x = y ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq21 y x
       grind)
    | exact superpose eq21 eq9
    | (have j1 := eq21 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq21 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq21 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1220 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq1212
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq1212
    | exact resolve eq1212 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq1221 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1220
       have i₂ := eq21 (σ y) (σ x)
       grind)
    | exact superpose eq21 eq1220
    | (have j1 := eq21 x y
       grind)
    | (have r₁ := eq1220
       have r₂ := eq21 (σ y) (σ x)
       grind)
    | (have r₁ := eq1220
       have r₂ := eq21 (M.op (σ x) (σ y)) (k (σ y) (σ x))
       grind)
    | (have r₁ := eq1220
       have r₂ := eq21 (k (σ y) (σ x)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1220 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1220
  have eq1223 : x = y ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1221
  have eq1299 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1223
       grind)
    | exact superpose eq1223 eq9
    | exact resolve eq9 eq1223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq1300 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1299
  have eq1301 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1300
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1300
    | exact resolve eq1300 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300
  have eq1302 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1301
  have eq1303 : (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1302
  have eq1381 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq1303
       grind)
    | exact superpose eq1303 eq10
    | exact resolve eq10 eq1303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1303
  have eq1383 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1381
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1381
    | exact resolve eq1381 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381
  have eq1384 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq1383
  have eq1387 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22 y y
       have i₂ := eq1384
       grind)
    | exact superpose eq1384 eq22
    | exact resolve eq22 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1434 : (k y y) = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1387
       have i₂ := eq22 x x
       grind)
    | exact superpose eq22 eq1387
    | exact resolve eq1387 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1387
  have eq1456 : (k x x) ≠ (k x x) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq566
       have i₂ := eq1434
       grind)
    | exact superpose eq1434 eq566
    | (have r₁ := eq566
       have r₂ := eq1434
       grind)
    | exact resolve eq566 eq1434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566 eq1434
  have eq1459 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1456
  have eq1463 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1459
       have i₂ := eq20 (σ x) (σ y)
       grind)
    | exact superpose eq20 eq1459
    | (have j1 := eq20 (σ x) (σ y)
       grind)
    | (have r₁ := eq1459
       have r₂ := eq20 (σ x) (σ y)
       grind)
    | (have r₁ := eq1459
       have r₂ := eq20 (M.op (σ x) (σ y)) (k (σ x) (σ y))
       grind)
    | (have r₁ := eq1459
       have r₂ := eq20 (k (σ x) (σ y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1459 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1459
  have eq1464 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq1463
  have eq1465 : x = y ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq1464
  have eq1467 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1465
       have r₂ := eq1384
       grind)
    | exact resolve eq1465 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384 eq1465
  have eq1468 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1467
       grind)
    | exact superpose eq1467 eq9
    | exact resolve eq9 eq1467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467
  have eq1469 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq1468
  have eq1470 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1469
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1469
    | exact resolve eq1469 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1469
  have eq1471 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1470
  have eq1472 : (σ x) = (σ y) := by grind
  clear eq1471
  have eq1474 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq1472
       grind)
    | exact superpose eq1472 eq15
    | exact resolve eq15 eq1472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472
  have eq1521 : x = y := by
    first
    | (have i₁ := eq1474
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq1474
    | exact resolve eq1474 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474
  have eq1524 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1521
       grind)
    | exact superpose eq1521 eq9
    | exact resolve eq9 eq1521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521
  have eq1525 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq1524
  have eq1526 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1525
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1525
    | exact resolve eq1525 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1525
  have eq1527 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by grind
  clear eq1526
  have eq1528 : False := by grind
  exact eq1528

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation422 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law422 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
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
  clear eq19
  have eq116 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq118 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
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
  have eq713 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq116 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq786 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq118 X0 X1
       grind)
    | exact superpose eq118 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq118 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) X0
       have r₂ := eq118 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq118 (M.op (τ X1) X0) X1
       grind)
    | exact resolve eq13 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq790 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq786 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq791 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq790 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq2294 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq791 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq791
    | exact resolve eq791 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq2338 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2294 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2294
    | (have j0 := eq2294 X0 X1
       grind)
    | exact resolve eq2294 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2294
  have eq2374 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq2338 X1 X0
       grind)
    | exact superpose eq2338 eq10
    | (have j1 := eq2338 X1 X0
       grind)
    | exact resolve eq10 eq2338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2417 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2374 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2374
    | (have j0 := eq2374 X0 X1
       grind)
    | exact resolve eq2374 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2374
  have eq2456 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq2417 X0 (σ X1)
       grind)
    | exact superpose eq2417 eq37
    | (have j1 := eq2417 X0 (σ X1)
       grind)
    | exact resolve eq37 eq2417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2417
  have eq4176 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) X0
       have i₂ := eq2456 (σ X0) X1
       grind)
    | exact superpose eq2456 eq28
    | (have j1 := eq2456 (σ X0) X1
       grind)
    | exact resolve eq28 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2456
  have eq4237 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4176 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4176
    | (have j0 := eq4176 X0 X1
       grind)
    | exact resolve eq4176 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4176
  have eq4271 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4237 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4237
    | (have j0 := eq4237 X0 X1
       grind)
    | exact resolve eq4237 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4237
  have eq4281 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4271 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4271
    | (have j0 := eq4271 X0 X1
       grind)
    | exact resolve eq4271 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4271
  have eq4482 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq4281 X1 X0
       grind)
    | exact superpose eq4281 eq11
    | (have j1 := eq4281 X1 X0
       grind)
    | exact resolve eq11 eq4281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4281
  have eq5360 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4482 y x
       grind)
    | exact superpose eq4482 eq16
    | (have j1 := eq4482 y x
       grind)
    | exact resolve eq16 eq4482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4482
  have eq5392 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5360
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq5360
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq5360
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5360
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5360 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5393 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq5360
       have i₂ := eq2338 y x
       grind)
    | exact superpose eq2338 eq5360
    | (have j1 := eq2338 y x
       grind)
    | (have r₁ := eq5360
       have r₂ := eq2338 y x
       grind)
    | (have r₁ := eq5360
       have r₂ := eq2338 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5360
       have r₂ := eq2338 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5360 eq2338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338 eq5360
  have eq5396 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5393
  have eq5397 : x = y ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq5396
  have eq5398 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5392
  have eq5399 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq5398
  have eq5403 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5397
       grind)
    | exact superpose eq5397 eq16
    | exact resolve eq16 eq5397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5397
  have eq5404 : x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5403
       have r₂ := eq22 x
       grind)
    | exact resolve eq5403 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5403
  have eq5408 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq713 x y
       have i₂ := eq5404
       grind)
    | exact superpose eq5404 eq713
    | (have j0 := eq713 x y
       grind)
    | exact resolve eq713 eq5404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713 eq5404
  have eq5415 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5408
  have eq5416 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5415
  have eq5420 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5399
       grind)
    | exact superpose eq5399 eq16
    | exact resolve eq16 eq5399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5399
  have eq5421 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5420
       have r₂ := eq22 x
       grind)
    | exact resolve eq5420 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5420
  have eq5435 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5416
       grind)
    | exact superpose eq5416 eq16
    | exact resolve eq16 eq5416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5416
  have eq5459 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5435
       have i₂ := eq5421
       grind)
    | exact superpose eq5421 eq5435
    | exact resolve eq5435 eq5421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5421 eq5435
  have eq5460 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq5459
  have eq5461 : (σ x) = (σ y) := by grind
  clear eq5460
  have eq5462 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5461
       grind)
    | exact superpose eq5461 eq16
    | exact resolve eq16 eq5461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5463 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5461
       grind)
    | exact superpose eq5461 eq10
    | exact resolve eq10 eq5461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5461
  have eq5516 : x = y := by
    first
    | (have i₁ := eq5463
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5463
    | exact resolve eq5463 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5463
  have eq5517 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5462
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5462
    | exact resolve eq5462 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5462
  have eq5518 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5517
       have i₂ := eq5516
       grind)
    | exact superpose eq5516 eq5517
    | exact resolve eq5517 eq5516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5516 eq5517
  have eq5519 : False := by grind
  exact eq5519

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation426 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
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
  have eq81 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq132 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq81 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq81 X0 X1
       grind)
    | exact superpose eq81 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq81 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq81 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq13 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq140 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq132 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq141 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq140 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq143 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq141 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq141
    | (have j0 := eq141 X0 X1
       grind)
    | exact resolve eq141 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq146 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq143 X0 X1
       have j1 := eq137 X1 X0
       grind)
    | (have r₁ := eq143 X1 X0
       have r₂ := eq137 X0 X1
       grind)
    | (have r₁ := eq143 X1 (k X0 X1)
       have r₂ := eq137 X0 X1
       grind)
    | (have r₁ := eq143 X1 X1
       have r₂ := eq137 X1 X1
       grind)
    | exact resolve eq143 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq143
  have eq503 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq146 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq146
    | exact resolve eq146 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq511 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq146 y x
       grind)
    | exact superpose eq146 eq16
    | (have j1 := eq146 y x
       grind)
    | exact resolve eq16 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq522 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq503 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq503
    | (have j0 := eq503 X0 X1
       grind)
    | exact resolve eq503 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq503
  have eq528 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq522 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq522
    | exact resolve eq522 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq628 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq528 (τ X0) X1
       grind)
    | exact superpose eq528 eq18
    | (have j1 := eq528 (τ X0) X1
       grind)
    | exact resolve eq18 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq528
  have eq828 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq628 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq628
    | exact resolve eq628 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq883 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq828 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq828
    | (have j0 := eq828 X0 X1
       grind)
    | exact resolve eq828 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq983 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq511
       have i₂ := eq883 x y
       grind)
    | exact superpose eq883 eq511
    | (have j1 := eq883 (σ x) (σ y)
       grind)
    | (have r₁ := eq511
       have r₂ := eq883 x y
       grind)
    | exact resolve eq511 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq984 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq983
  have eq1014 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq984
  have eq1018 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq511
       have i₂ := eq1014
       grind)
    | exact superpose eq1014 eq511
    | exact resolve eq511 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511 eq1014
  have eq1019 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1018
  have eq1020 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1019
  have eq1072 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1020
  have eq1077 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1072
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1072
    | exact resolve eq1072 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1082 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1077
       grind)
    | exact superpose eq1077 eq16
    | exact resolve eq16 eq1077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1138 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1082
       have i₂ := eq883 x y
       grind)
    | exact superpose eq883 eq1082
    | (have j1 := eq883 x y
       grind)
    | (have r₁ := eq1082
       have r₂ := eq883 x y
       grind)
    | exact resolve eq1082 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883
  have eq1139 : x = (M.op y y) := by grind
  clear eq1138
  have eq1144 : (M.op x y) = (k x y) := by grind
  clear eq1139
  have eq1216 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1082
       have i₂ := eq1144
       grind)
    | exact superpose eq1144 eq1082
    | exact resolve eq1082 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082 eq1144
  have eq1219 : False := by grind
  exact eq1219

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation426 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X0 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq21 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq52 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq52 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq52 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq53 (σ X0)
       grind)
    | exact superpose eq53 eq15
    | exact resolve eq15 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq53 (τ X0)
       grind)
    | exact superpose eq53 eq18
    | exact resolve eq18 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq58
    | exact resolve eq58 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq55 X0
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq61
    | exact resolve eq61 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq73 : ∀ X0 X1 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq64
    | exact resolve eq64 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq82
    | (have j0 := eq82 X0 X1
       grind)
    | exact resolve eq82 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq64 X1
       grind)
    | exact superpose eq64 eq89
    | (have j0 := eq89 X0 X1
       grind)
    | exact resolve eq89 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq89
  have eq127 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | (have j0 := eq91 X0 X1
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq91 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq91
    | (have j0 := eq91 X0 X2
       grind)
    | exact resolve eq91 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq150 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq128 X0 X1 X2
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq128
    | (have j0 := eq128 X0 X1 X2
       grind)
    | exact resolve eq128 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq128
  have eq151 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq127 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq127
    | (have j0 := eq127 X0 X1
       grind)
    | exact resolve eq127 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq155 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq151 X0 X1
       have j1 := eq76 X1 X0
       grind)
    | (have r₁ := eq151 X0 X0
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq151 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq159 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq155 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq155
    | (have j0 := eq155 X0 X1
       grind)
    | exact resolve eq155 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq155
  have eq402 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq159 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq159
    | exact resolve eq159 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq1302 : ∀ X0 X1 X2 X3 : G, (M.op (k X0 (σ X1)) (σ X2)) ≠ (M.op (k X0 (σ X1)) X3) ∨ (M.op (k X0 (σ X1)) (σ X2)) = (k (k X0 (σ X1)) X3) ∨ (M.op X3 X3) = X3 ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (k X0 (σ X1)) X1
       have i₂ := eq150 X0 X1 X2
       grind)
    | exact superpose eq150 eq13
    | (have j0 := eq13 X0 X3
       have j1 := eq150 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) (σ X2)
       have r₂ := eq150 X0 X1 X2
       grind)
    | exact resolve eq13 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq49460 : ∀ X0 X1 X2 : G, (k (k X0 (σ X1)) (σ X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1302 X0 X1 X2 (σ X2)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302
  have eq49463 : ∀ X0 X1 X2 : G, (k (k X0 (σ X1)) (σ X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq49460 X0 X1 X2
       have j1 := eq12 (k X0 (σ X1)) (σ X2)
       grind)
    | (have r₁ := eq49460 X0 X1 X2
       have r₂ := eq12 X0 (σ X2)
       grind)
    | exact resolve eq49460 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49460
  have eq49531 : ∀ X0 X1 X2 : G, (k (k X0 (σ X1)) (σ X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq49463 X0 X1 X2
       have j1 := eq76 X2 (k X0 (σ X1))
       grind)
    | (have r₁ := eq49463 X0 X1 X0
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq49463 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq49463
  have eq49581 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49531 X0 X1 X2
       have i₂ := eq21 X0 X1 X2
       grind)
    | exact superpose eq21 eq49531
    | (have j0 := eq49531 X0 X1 X2
       grind)
    | exact resolve eq49531 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq49531
  have eq49582 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq49581 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49581
  have eq49825 : ∀ X0 X1 X2 : G, (k (σ (k (τ X0) X1)) X2) = (M.op (k X0 (σ X1)) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X2 (k (τ X0) X1)
       have i₂ := eq49582 X0 X1 (τ X2)
       grind)
    | exact superpose eq49582 eq18
    | exact resolve eq18 eq49582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq49582
  have eq49962 : ∀ X0 X1 X2 : G, (k (σ (k (τ X0) X1)) X2) = (M.op (k X0 (σ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49825 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq49825
    | exact resolve eq49825 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49825
  have eq50122 : ∀ X0 X1 X2 : G, (k (k X0 (σ X1)) X2) = (M.op (k X0 (σ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49962 X0 X1 X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq49962
    | exact resolve eq49962 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq49962
  have eq50285 : ∀ X0 X1 X2 : G, (k (k X1 X0) X2) = (M.op (k X1 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50122 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq50122
    | exact resolve eq50122 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50122
  have eq51479 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq50285 X0 X0 x
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq50285
    | exact resolve eq50285 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq51480 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = (M.op (M.op X0 X1) X2) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50285 X0 X1 X2
       have i₂ := eq402 X0 X1
       grind)
    | exact superpose eq402 eq50285
    | (have j1 := eq402 X2 (M.op X0 X1)
       grind)
    | exact resolve eq50285 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402 eq50285
  have eq487398 : ∀ X0 X2 : G, (M.op X0 X0) = X0 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq51480 X0 (M.op x (M.op X0 (M.op X0 X0))) X2
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq51480
    | exact resolve eq51480 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51480
  have eq487997 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51479 X0 X1
       have i₂ := eq487398 X0 X2
       grind)
    | exact superpose eq487398 eq51479
    | (have j1 := eq487398 X0 X1
       grind)
    | exact resolve eq51479 eq487398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51479 eq487398
  have eq493922 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq487997 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487997
  have eq493923 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq493922 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493922
  have eq494320 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq493923 (σ X0) (σ X1)
       grind)
    | exact superpose eq493923 eq15
    | exact resolve eq15 eq493923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq494754 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq494320 X0 X1
       have i₂ := eq493923 X0 X1
       grind)
    | exact superpose eq493923 eq494320
    | exact resolve eq494320 eq493923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493923 eq494320
  have eq544103 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq494754 x y
       grind)
    | exact superpose eq494754 eq16
    | (have r₁ := eq16
       have r₂ := eq494754 x y
       grind)
    | exact resolve eq16 eq494754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494754
  have eq544359 : False := by grind
  exact eq544359

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation426 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law426 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
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
  have eq112 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
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
  have eq113 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
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
  have eq114 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq641 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (τ X1)
       have i₂ := eq113 X0 X1
       grind)
    | exact superpose eq113 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq113 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq113 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) X1
       have r₂ := eq113 (M.op (τ X1) X1) X1
       grind)
    | exact resolve eq13 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq644 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq641 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq645 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq644 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq720 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq798 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq112 X0 X1
       grind)
    | exact superpose eq112 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq112 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq112 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X1
       have r₂ := eq112 (M.op (σ X1) X1) X1
       grind)
    | exact resolve eq13 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq802 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq798 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq803 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq802 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq2153 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq645 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq645
    | exact resolve eq645 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq2195 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2153 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2153
    | (have j0 := eq2153 X0 X1
       grind)
    | exact resolve eq2153 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153
  have eq3936 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq803 (σ X0) X1
       grind)
    | exact superpose eq803 eq37
    | (have j1 := eq803 (σ X1) X0
       grind)
    | exact resolve eq37 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq803
  have eq4000 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3936 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3936
    | (have j0 := eq3936 X0 X1
       grind)
    | exact resolve eq3936 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3936
  have eq4031 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4000 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4000
    | (have j0 := eq4000 X0 X1
       grind)
    | exact resolve eq4000 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4000
  have eq4040 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4031 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4031
    | (have j0 := eq4031 X0 X1
       grind)
    | exact resolve eq4031 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4031
  have eq4315 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4040 X0 X1
       grind)
    | exact superpose eq4040 eq11
    | (have j1 := eq4040 X0 X1
       grind)
    | exact resolve eq11 eq4040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4040
  have eq5185 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4315 x y
       grind)
    | exact superpose eq4315 eq16
    | (have j1 := eq4315 x y
       grind)
    | exact resolve eq16 eq4315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4315
  have eq5213 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5185
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq5185
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq5185
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5185
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5185 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5214 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq5185
       have i₂ := eq2195 y x
       grind)
    | exact superpose eq2195 eq5185
    | (have j1 := eq2195 y x
       grind)
    | (have r₁ := eq5185
       have r₂ := eq2195 y x
       grind)
    | (have r₁ := eq5185
       have r₂ := eq2195 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5185
       have r₂ := eq2195 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5185 eq2195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2195 eq5185
  have eq5217 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5214
  have eq5218 : x = y ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq5217
  have eq5219 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5213
  have eq5220 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5219
  have eq5224 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5218
       grind)
    | exact superpose eq5218 eq16
    | exact resolve eq16 eq5218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5218
  have eq5225 : x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5224
       have r₂ := eq22 x
       grind)
    | exact resolve eq5224 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5224
  have eq5230 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq720 x y
       have i₂ := eq5225
       grind)
    | exact superpose eq5225 eq720
    | (have j0 := eq720 x y
       grind)
    | exact resolve eq720 eq5225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720 eq5225
  have eq5236 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5230
  have eq5237 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5236
  have eq5249 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5237
       grind)
    | exact superpose eq5237 eq16
    | exact resolve eq16 eq5237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5237
  have eq5265 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5249
       have i₂ := eq5220
       grind)
    | exact superpose eq5220 eq5249
    | exact resolve eq5249 eq5220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5220 eq5249
  have eq5266 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5265
  have eq5267 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq5266
  have eq5268 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5267
       grind)
    | exact superpose eq5267 eq16
    | exact resolve eq16 eq5267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5267
  have eq5269 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq5268
       have r₂ := eq22 x
       grind)
    | exact resolve eq5268 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5268
  have eq5270 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5269
       grind)
    | exact superpose eq5269 eq16
    | exact resolve eq16 eq5269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5271 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5269
       grind)
    | exact superpose eq5269 eq10
    | exact resolve eq10 eq5269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5269
  have eq5323 : x = y := by
    first
    | (have i₁ := eq5271
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5271
    | exact resolve eq5271 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5271
  have eq5324 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5270
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5270
    | exact resolve eq5270 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5270
  have eq5325 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5324
       have i₂ := eq5323
       grind)
    | exact superpose eq5323 eq5324
    | exact resolve eq5324 eq5323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5323 eq5324
  have eq5326 : False := by grind
  exact eq5326
