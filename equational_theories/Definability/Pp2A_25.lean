import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation630 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
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
  have eq719 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq153 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq787 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
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
  have eq797 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq787 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq798 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq797 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq2707 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq798 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq798
    | exact resolve eq798 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq2752 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2707 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2707
    | (have j0 := eq2707 X0 X1
       grind)
    | exact resolve eq2707 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2707
  have eq2788 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq2752 X1 X0
       grind)
    | exact superpose eq2752 eq10
    | (have j1 := eq2752 X1 X0
       grind)
    | exact resolve eq10 eq2752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2831 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2788 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2788
    | (have j0 := eq2788 X0 X1
       grind)
    | exact resolve eq2788 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2788
  have eq2847 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq2831 X0 (σ X1)
       grind)
    | exact superpose eq2831 eq28
    | (have j1 := eq2831 X0 (σ X1)
       grind)
    | exact resolve eq28 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2831
  have eq5150 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq2847 (σ X0) X1
       grind)
    | exact superpose eq2847 eq37
    | (have j1 := eq2847 (σ X0) X1
       grind)
    | exact resolve eq37 eq2847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2847
  have eq5215 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5150 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5150
    | (have j0 := eq5150 X0 X1
       grind)
    | exact resolve eq5150 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5150
  have eq5247 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5215 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5215
    | (have j0 := eq5215 X0 X1
       grind)
    | exact resolve eq5215 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5215
  have eq5257 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5247 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5247
    | (have j0 := eq5247 X0 X1
       grind)
    | exact resolve eq5247 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5247
  have eq5421 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5257 (τ X1) (τ X0)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq5257
    | (have j0 := eq5257 (τ X0) (τ X1)
       grind)
    | exact resolve eq5257 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq5257
  have eq5620 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) X1)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5421 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5421
    | (have j0 := eq5421 X0 X1
       grind)
    | exact resolve eq5421 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5421
  have eq5696 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5620 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5620
    | (have j0 := eq5620 X0 X1
       grind)
    | exact resolve eq5620 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5620
  have eq5756 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5696 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5696
    | (have j0 := eq5696 X0 X1
       grind)
    | exact resolve eq5696 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5696
  have eq5814 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5756 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5756
    | (have j0 := eq5756 X0 X1
       grind)
    | exact resolve eq5756 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5756
  have eq5903 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq5814 X0 X1
       grind)
    | exact superpose eq5814 eq11
    | (have j1 := eq5814 X0 X1
       grind)
    | exact resolve eq11 eq5814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5814
  have eq6025 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5903 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq5903
    | (have j0 := eq5903 X0 X1
       grind)
    | exact resolve eq5903 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5903
  have eq6095 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6025 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6025
    | (have j0 := eq6025 (τ (σ X0)) (τ (σ (k X0 X1)))
       grind)
    | exact resolve eq6025 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6025
  have eq6265 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6095 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq6095
    | (have j0 := eq6095 X0 X1
       grind)
    | exact resolve eq6095 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6095
  have eq6270 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6265 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6265
    | (have j0 := eq6265 X0 X1
       grind)
    | exact resolve eq6265 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6265
  have eq6798 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6270 x y
       grind)
    | exact superpose eq6270 eq16
    | (have j1 := eq6270 x y
       grind)
    | exact resolve eq16 eq6270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6270
  have eq6822 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6798
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq6798
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq6798
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq6798
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6798 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6823 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq6798
       have i₂ := eq2752 y x
       grind)
    | exact superpose eq2752 eq6798
    | (have j1 := eq2752 y x
       grind)
    | (have r₁ := eq6798
       have r₂ := eq2752 y x
       grind)
    | (have r₁ := eq6798
       have r₂ := eq2752 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq6798
       have r₂ := eq2752 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6798 eq2752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2752 eq6798
  have eq6826 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by grind
  clear eq6823
  have eq6827 : x = y ∨ x = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq6826
  have eq6828 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq6822
  have eq6829 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6828
  have eq6832 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6827
       grind)
    | exact superpose eq6827 eq16
    | exact resolve eq16 eq6827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6827
  have eq6833 : x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6832
       have r₂ := eq22 x
       grind)
    | exact resolve eq6832 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6832
  have eq6837 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq719 x y
       have i₂ := eq6833
       grind)
    | exact superpose eq6833 eq719
    | (have j0 := eq719 x y
       grind)
    | exact resolve eq719 eq6833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719 eq6833
  have eq6844 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq6837
  have eq6845 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq6844
  have eq6857 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6845
       grind)
    | exact superpose eq6845 eq16
    | exact resolve eq16 eq6845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6845
  have eq6871 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6857
       have i₂ := eq6829
       grind)
    | exact superpose eq6829 eq6857
    | exact resolve eq6857 eq6829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6829 eq6857
  have eq6872 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6871
  have eq6873 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq6872
  have eq6874 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6873
       grind)
    | exact superpose eq6873 eq16
    | exact resolve eq16 eq6873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6873
  have eq6875 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq6874
       have r₂ := eq22 x
       grind)
    | exact resolve eq6874 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6874
  have eq6876 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6875
       grind)
    | exact superpose eq6875 eq16
    | exact resolve eq16 eq6875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6877 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6875
       grind)
    | exact superpose eq6875 eq10
    | exact resolve eq10 eq6875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6875
  have eq6930 : x = y := by
    first
    | (have i₁ := eq6877
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6877
    | exact resolve eq6877 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6877
  have eq6931 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq6876
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq6876
    | exact resolve eq6876 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6876
  have eq6932 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq6931
       have i₂ := eq6930
       grind)
    | exact superpose eq6930 eq6931
    | exact resolve eq6931 eq6930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6930 eq6931
  have eq6933 : False := by grind
  exact eq6933

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyx_y_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq98
    | exact resolve eq98 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq111
    | exact resolve eq111 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq605 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
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
  have eq810 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq605 X1 x X3
       have i₂ := eq605 X1 x X0
       grind)
    | exact superpose eq605 eq605
    | exact resolve eq605 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq822 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 x
       have i₂ := eq605 X1 x X0
       grind)
    | exact superpose eq605 eq14
    | exact resolve eq14 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq857 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq822 X0 (M.op X0 X0)
       have i₂ := eq822 X0 X0
       grind)
    | exact superpose eq822 eq822
    | exact resolve eq822 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq964 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq857 X0
       grind)
    | exact superpose eq857 eq14
    | exact resolve eq14 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq1409 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq810 X0 (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq822 X1 X0
       grind)
    | exact superpose eq822 eq810
    | exact resolve eq810 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq822
  have eq23210 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq112 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23211 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23210
    | exact resolve eq23210 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23210
  have eq23222 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq23211
       have r₂ := eq28
       grind)
    | exact resolve eq23211 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23211
  have eq23236 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X0 (M.op (σ y) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq23222 eq1409
    | exact resolve eq1409 eq23222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23222
  have eq23244 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq23236 x
       have i₂ := eq964 sF3 x
       grind)
    | exact superpose eq964 eq23236
    | exact resolve eq23236 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23236
  have eq23245 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq23244
  have eq23251 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq23245
  have eq23305 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23251
    | exact resolve eq23251 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23251
  have eq24048 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23305 eq112
    | exact resolve eq112 eq23305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq23305
  have eq24060 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq24048
  have eq24062 : y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq24060
       have r₂ := eq28
       grind)
    | exact resolve eq24060 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24060
  have eq24076 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op X0 (M.op y y))) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1409 x y X0
       have i₂ := eq24062
       grind)
    | exact superpose eq24062 eq1409
    | exact resolve eq1409 eq24062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24062
  have eq24084 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24076 x
       have i₂ := eq964 y x
       grind)
    | exact superpose eq964 eq24076
    | exact resolve eq24076 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24076
  have eq24085 : y = (M.op x x) := by grind
  clear eq24084
  have eq24091 : (M.op x y) = (k y x) := by grind
  clear eq24085
  have eq24145 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq24091
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24091
    | exact resolve eq24091 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq24091
  have eq25064 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq24145
       grind)
    | exact superpose eq24145 eq70
    | exact resolve eq70 eq24145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq24145
  have eq25090 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21 eq25064
    | exact resolve eq25064 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq25064
  have eq25571 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25090 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq25090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25572 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq25571
    | exact resolve eq25571 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25571
  have eq25583 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq25572
       have r₂ := eq28
       grind)
    | exact resolve eq25572 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25572
  have eq35673 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X0 (M.op (σ y) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq25583 eq1409
    | exact resolve eq1409 eq25583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409 eq25583
  have eq35681 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq35673 x
       have i₂ := eq964 sF3 x
       grind)
    | exact superpose eq964 eq35673
    | exact resolve eq35673 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964 eq35673
  have eq35682 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq35681
  have eq36064 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq35682
  have eq36118 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25090 eq36064
    | exact resolve eq36064 eq25090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25090 eq36064
  have eq36126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq36118
    | exact resolve eq36118 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq36118
  have eq36128 : False := by grind
  exact eq36128

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_x_pyx_Equation723 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
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
  have eq25 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
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
  have eq27 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq18
  have eq31 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq27 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq31
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq73 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq10
    | exact resolve eq10 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq94 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))) = (M.op (M.op X3 (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) (M.op X1 (M.op (M.op X2 X0) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 (M.op X1 (M.op (M.op X2 X0) X0)) X1 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq9 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2))) (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2))) X1
       have i₂ := eq25 (M.op (M.op X1 X2) X2) X3 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0)))) = (M.op X4 (M.op X4 (M.op (M.op X2 (M.op (M.op X3 X0) X0)) (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 (M.op X1 (M.op (M.op X2 X0) X0)) X1 X2 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op X4 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))))) = (M.op X5 (M.op X5 (M.op (M.op X4 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))) (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op X4 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2))))))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0)))) X1 X2 X1
       have i₂ := eq24 X0 X1 X2 X3
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X0 X2 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))) (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))) = (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2))) (M.op X3 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))) X3
       have i₂ := eq24 X2 (M.op X3 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))) X0 X1
       grind)
    | exact superpose eq24 eq25
    | exact resolve eq25 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq145 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq135 y x
       grind)
    | exact superpose eq135 eq16
    | (have j1 := eq135 y x
       grind)
    | exact resolve eq16 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq163 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (M.op (τ (M.op X0 X0)) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1 (τ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq9
    | exact resolve eq9 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq145
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq145
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq145
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq145
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq145 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq536 : x = y ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) := by grind
  clear eq535
  have eq571 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X2 X0))) = (M.op (M.op X2 X0) (M.op (M.op X0 (M.op (M.op X1 X0) X0)) (M.op X2 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq108 (M.op X2 X0) X2 X3
       have i₂ := eq108 X0 X1 X2
       grind)
    | exact superpose eq108 eq108
    | exact resolve eq108 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ X0))) = (M.op X1 (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq108 (τ X0) (τ X0) X1
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq108
    | exact resolve eq108 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq601 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op X2 (M.op X2 (M.op (M.op X0 (M.op (M.op X1 X0) X0)) (M.op X3 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X3 X0) X2 X3
       have i₂ := eq108 X0 X1 X3
       grind)
    | exact superpose eq108 eq9
    | exact resolve eq9 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1108 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (M.op X0 (M.op X0 (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq163 X1 (τ X1)
       have i₂ := eq575 X1 X0
       grind)
    | exact superpose eq575 eq163
    | exact resolve eq163 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq575
  have eq1169 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1108 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1108
    | exact resolve eq1108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq1189 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X2 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq97 X0 X0 X1
       have i₂ := eq108 X0 X1 X2
       grind)
    | exact superpose eq108 eq97
    | exact resolve eq97 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1252 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1169 (M.op X0 X0) X0
       have i₂ := eq1169 X0 X0
       grind)
    | exact superpose eq1169 eq1169
    | exact resolve eq1169 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1257 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op X2 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 (M.op X2 X0)) X1 X0
       have i₂ := eq1169 X0 X2
       grind)
    | exact superpose eq1169 eq9
    | exact resolve eq9 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1260 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 (M.op X1 (M.op X1 X0)) X1 X0
       have i₂ := eq1169 X0 X1
       grind)
    | exact superpose eq1169 eq25
    | exact resolve eq25 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1268 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1260 X0 X1 X2
       have i₂ := eq1169 X0 X1
       grind)
    | exact superpose eq1169 eq1260
    | exact resolve eq1260 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260
  have eq1270 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1257 X0 X1 X2
       have i₂ := eq1169 X0 X2
       grind)
    | exact superpose eq1169 eq1257
    | exact resolve eq1257 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257
  have eq1282 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1 X0
       have i₂ := eq1252 X0
       grind)
    | exact superpose eq1252 eq25
    | exact resolve eq25 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq1283 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq1252 X0
       grind)
    | exact superpose eq1252 eq9
    | exact resolve eq9 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1291 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1169 X0 (M.op X0 X0)
       have i₂ := eq1252 X0
       grind)
    | exact superpose eq1252 eq1169
    | exact resolve eq1169 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1936 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X2) (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X0 X1 X2 x
       have i₂ := eq97 (M.op (M.op X1 X2) X2) x X0
       grind)
    | exact superpose eq97 eq100
    | exact resolve eq100 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq1937 : ∀ X1 X2 : G, (M.op (M.op (M.op X1 X2) X2) (M.op X2 (M.op (M.op X1 X2) X2))) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq1936 x X1 X2
       have i₂ := eq97 X2 x X1
       grind)
    | exact superpose eq97 eq1936
    | exact resolve eq1936 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1936
  have eq1947 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq97 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X0
       have i₂ := eq1291 X0
       grind)
    | exact superpose eq1291 eq97
    | exact resolve eq97 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1960 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1947 X0 X1
       have i₂ := eq1291 X0
       grind)
    | exact superpose eq1291 eq1947
    | exact resolve eq1947 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1947
  have eq1971 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1960 X0 X1
       have i₂ := eq1282 X0 (M.op X0 X0)
       grind)
    | exact superpose eq1282 eq1960
    | exact resolve eq1960 eq1282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960
  have eq2019 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 (M.op (M.op X1 X0) X0)))) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) (M.op X0 (M.op X0 (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq108 (M.op X0 (M.op (M.op X1 X0) X0)) (M.op (M.op X1 X0) X0) X2
       have i₂ := eq1937 X1 X0
       grind)
    | exact superpose eq1937 eq108
    | exact resolve eq108 eq1937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2025 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X0) = (M.op X2 (M.op X2 (M.op X0 (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2019 X0 X1 X2
       have i₂ := eq1268 (M.op (M.op X1 X0) X0) X0 X0
       grind)
    | exact superpose eq1268 eq2019
    | exact resolve eq2019 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2019
  have eq2083 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1169 X0 (M.op X1 X0)
       have i₂ := eq1971 X0 X1
       grind)
    | exact superpose eq1971 eq1169
    | exact resolve eq1169 eq1971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq2284 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X0)))) = (M.op X4 (M.op X4 (M.op (M.op X2 (M.op X0 X0)) (M.op X1 (M.op X0 (M.op X2 (M.op X0 X0))))))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq101 X0 X1 X2 X1 X4
       have i₂ := eq1971 X0 X1
       grind)
    | exact superpose eq1971 eq101
    | exact resolve eq101 eq1971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq2403 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))))) = (M.op (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) (M.op (M.op X0 X0) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq2284 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)) X0 (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq2284 X0 (M.op X0 X0) (M.op X0 X0) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))
       grind)
    | exact superpose eq2284 eq2284
    | exact resolve eq2284 eq2284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2438 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X4 (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))))) = (M.op (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))) (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq108 (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))) X3 X4
       have i₂ := eq2284 X1 X0 X2 X3
       grind)
    | exact superpose eq2284 eq108
    | exact resolve eq108 eq2284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2462 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq2403 X0
       have i₂ := eq1291 X0
       grind)
    | exact superpose eq1291 eq2403
    | exact resolve eq2403 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2403
  have eq2475 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2462 X0
       have i₂ := eq1252 X0
       grind)
    | exact superpose eq1252 eq2462
    | exact resolve eq2462 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2462
  have eq2478 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2475 X0
       have i₂ := eq1252 (M.op X0 X0)
       grind)
    | exact superpose eq1252 eq2475
    | exact resolve eq2475 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2475
  have eq2827 : ∀ X0 X2 X3 : G, (M.op (M.op X0 (M.op X2 X2)) (M.op X2 (M.op X0 (M.op X2 X2)))) = (M.op (M.op X3 (M.op X2 (M.op X0 (M.op X2 X2)))) (M.op X2 (M.op X0 (M.op X2 X2)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq112 X0 x X0 X3
       have i₂ := eq1971 X0 x
       grind)
    | exact superpose eq1971 eq112
    | exact resolve eq112 eq1971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq2828 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op X2 X2)) (M.op X2 (M.op X0 (M.op X2 X2)))) = (M.op (M.op X2 (M.op X0 (M.op X2 X2))) (M.op X2 (M.op X0 (M.op X2 X2)))) := by
    intro X0 X2
    first
    | (have i₁ := eq2827 X0 X2 x
       have i₂ := eq1971 (M.op X2 (M.op X0 (M.op X2 X2))) x
       grind)
    | exact superpose eq1971 eq2827
    | exact resolve eq2827 eq1971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2827
  have eq3503 : ∀ X0 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X0 (M.op X2 X2)) (M.op X4 (M.op X2 (M.op X0 (M.op X2 X2)))))) = (M.op X5 (M.op X5 (M.op (M.op X4 (M.op X2 (M.op X0 (M.op X2 X2)))) (M.op X3 (M.op (M.op X0 (M.op X2 X2)) (M.op X4 (M.op X2 (M.op X0 (M.op X2 X2))))))))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq102 X0 x X0 X3 X4 X5
       have i₂ := eq1971 X0 x
       grind)
    | exact superpose eq1971 eq102
    | exact resolve eq102 eq1971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq3576 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))) = (M.op X3 (M.op X3 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3503 X2 X1 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))) X0 X3
       have i₂ := eq2284 X1 X0 X2 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1))))
       grind)
    | exact superpose eq2284 eq3503
    | exact resolve eq3503 eq2284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2284 eq3503
  have eq3963 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq2025 X0 x X2
       have i₂ := eq1971 X0 x
       grind)
    | exact superpose eq1971 eq2025
    | exact resolve eq2025 eq1971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2025
  have eq3973 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X0)) = (M.op (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3963 (M.op (M.op X1 X0) X0) X2
       have i₂ := eq9 X0 (M.op (M.op X1 X0) X0) X1
       grind)
    | exact superpose eq9 eq3963
    | exact resolve eq3963 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4055 : ∀ X0 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq3973 X0 x X2
       have i₂ := eq1971 X0 x
       grind)
    | exact superpose eq1971 eq3973
    | exact resolve eq3973 eq1971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3973
  have eq5570 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op (M.op X1 X0) X0)) (M.op X0 (M.op (M.op X1 X0) X0))) = (M.op (M.op (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0)) (M.op (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4055 (M.op (M.op X1 X0) X0) (M.op X2 (M.op (M.op X1 X0) X0))
       have i₂ := eq97 X0 X2 X1
       grind)
    | exact superpose eq97 eq4055
    | exact resolve eq4055 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq5635 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) = (M.op (M.op X1 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2478 (M.op X0 X0)
       have i₂ := eq4055 X0 x
       grind)
    | exact superpose eq4055 eq2478
    | exact resolve eq2478 eq4055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5789 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5635 X0 X1
       have i₂ := eq1268 X1 X0 X1
       grind)
    | exact superpose eq1268 eq5635
    | exact resolve eq5635 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5635
  have eq5826 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op (M.op X1 X0) X0)) (M.op X0 (M.op (M.op X1 X0) X0))) = (M.op (M.op (M.op X1 X0) X0) (M.op (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5570 X0 X1 X2
       have i₂ := eq2478 (M.op (M.op X1 X0) X0)
       grind)
    | exact superpose eq2478 eq5570
    | exact resolve eq5570 eq2478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2478 eq5570
  have eq5856 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op (M.op X1 X0) X0)) (M.op X0 (M.op (M.op X1 X0) X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5826 X0 X1 X2
       have i₂ := eq9 X0 (M.op (M.op X1 X0) X0) X1
       grind)
    | exact superpose eq9 eq5826
    | exact resolve eq5826 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5826
  have eq5868 : ∀ X0 X2 : G, (M.op (M.op X2 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq5856 X0 x X2
       have i₂ := eq1971 X0 x
       grind)
    | exact superpose eq1971 eq5856
    | exact resolve eq5856 eq1971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5856
  have eq6528 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) X0)) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5789 X1 (M.op X1 (M.op (M.op X2 X0) X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq5789
    | exact resolve eq5789 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6642 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4055 (M.op X0 (M.op X0 X1)) X2
       have i₂ := eq5789 X0 X1
       grind)
    | exact superpose eq5789 eq4055
    | exact resolve eq4055 eq5789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6733 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6528 X0 X1 x
       have i₂ := eq1971 X0 x
       grind)
    | exact superpose eq1971 eq6528
    | exact resolve eq6528 eq1971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6528
  have eq7266 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X1 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5868 X1 (M.op X1 X1)
       have i₂ := eq4055 X1 X0
       grind)
    | exact superpose eq4055 eq5868
    | exact resolve eq5868 eq4055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7274 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 (M.op X0 X1))) (M.op (M.op X1 X1) (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5868 (M.op X0 X0) X2
       have i₂ := eq4055 X0 X2
       grind)
    | exact superpose eq4055 eq5868
    | exact resolve eq5868 eq4055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7281 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5868 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq3963 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq3963 eq5868
    | exact resolve eq5868 eq3963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3963
  have eq7397 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7281 X0 X1
       have i₂ := eq5868 X0 X0
       grind)
    | exact superpose eq5868 eq7281
    | exact resolve eq7281 eq5868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7281
  have eq7401 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 (M.op X0 X1))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7274 X0 X1 X2
       have i₂ := eq1268 X1 X0 X1
       grind)
    | exact superpose eq1268 eq7274
    | exact resolve eq7274 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7274
  have eq12759 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7401 X1 (M.op X1 X0) X1
       have i₂ := eq6642 X0 X1 X1
       grind)
    | exact superpose eq6642 eq7401
    | exact resolve eq7401 eq6642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6642
  have eq12760 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op X0 (M.op X1 X2))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7401 X1 X2 X1
       have i₂ := eq1270 (M.op X1 X2) X0 X1
       grind)
    | (have i₁ := eq7401 X1 X2 X1
       have i₂ := eq1270 (M.op X1 X2) X1 X0
       grind)
    | exact superpose eq1270 eq7401
    | exact resolve eq7401 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270 eq7401
  have eq12887 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12759 X0 X1
       have i₂ := eq6733 X0 X1
       grind)
    | exact superpose eq6733 eq12759
    | exact resolve eq12759 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12759
  have eq14951 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq536
       grind)
    | exact superpose eq536 eq16
    | exact resolve eq16 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq14952 : (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq14951
       have r₂ := eq22 x
       grind)
    | exact resolve eq14951 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14951
  have eq40673 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 (M.op X0 X1)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1189 X0 X1 x
       have i₂ := eq1971 X1 x
       grind)
    | exact superpose eq1971 eq1189
    | exact resolve eq1189 eq1971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189
  have eq40730 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) = (M.op (M.op (M.op X3 (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op X1 (M.op (M.op X2 X0) X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq40673 (M.op X3 (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) (M.op X1 (M.op (M.op X2 X0) X0))
       have i₂ := eq94 X0 X1 X2 X3
       grind)
    | exact superpose eq94 eq40673
    | exact resolve eq40673 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq41028 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) = (M.op (M.op (M.op X3 (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) (M.op X1 (M.op (M.op (M.op X2 X0) X0) (M.op (M.op X2 X0) X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq40730 X0 X1 X2 X3
       have i₂ := eq6733 (M.op (M.op X2 X0) X0) X1
       grind)
    | exact superpose eq6733 eq40730
    | exact resolve eq40730 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40730
  have eq41154 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) = (M.op (M.op (M.op X3 (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) (M.op X1 (M.op (M.op X2 X0) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq41028 X0 X1 X2 X3
       have i₂ := eq6733 X0 (M.op X2 X0)
       grind)
    | exact superpose eq6733 eq41028
    | exact resolve eq41028 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41028
  have eq41233 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) = (M.op (M.op (M.op X3 (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq41154 X0 X1 X2 X3
       have i₂ := eq7397 X0 X2
       grind)
    | exact superpose eq7397 eq41154
    | exact resolve eq41154 eq7397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41154
  have eq41283 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))) (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) = (M.op (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))) (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41233 X0 X1 X2 X1
       have i₂ := eq1971 (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))) X1
       grind)
    | exact superpose eq1971 eq41233
    | exact resolve eq41233 eq1971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41233
  have eq41310 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op X1 (M.op (M.op X2 X0) X0)))) = (M.op (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op X1 (M.op (M.op X2 X0) X0)))) (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41283 X1 X1 X2
       have i₂ := eq6733 (M.op X1 (M.op (M.op X2 X1) X1)) X1
       grind)
    | exact superpose eq6733 eq41283
    | exact resolve eq41283 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41283
  have eq41327 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op (M.op X2 X0) X0) (M.op (M.op X2 X0) X0)))) = (M.op (M.op X0 (M.op X1 (M.op (M.op (M.op X2 X0) X0) (M.op (M.op X2 X0) X0)))) (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41310 X0 X1 X2
       have i₂ := eq6733 (M.op (M.op X2 X0) X0) X1
       grind)
    | exact superpose eq6733 eq41310
    | exact resolve eq41310 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41310
  have eq41338 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X0) (M.op X0 X0)))) = (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X0) (M.op X0 X0)))) (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41327 X0 X1 X2
       have i₂ := eq6733 X0 (M.op X2 X0)
       grind)
    | exact superpose eq6733 eq41327
    | exact resolve eq41327 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41327
  have eq41343 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X0 (M.op X1 (M.op X0 (M.op X0 X0)))) (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq41338 X0 X1 X1
       have i₂ := eq7397 X0 X1
       grind)
    | exact superpose eq7397 eq41338
    | exact resolve eq41338 eq7397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7397 eq41338
  have eq41346 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (M.op X0 X0))) (M.op X1 (M.op X0 (M.op X0 X0)))) = (M.op X0 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq41343 X0 X1
       have i₂ := eq1971 (M.op X1 (M.op X0 (M.op X0 X0))) X0
       grind)
    | exact superpose eq1971 eq41343
    | exact resolve eq41343 eq1971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41343
  have eq41348 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op X0 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq41346 X0 X1
       have i₂ := eq6733 (M.op X0 (M.op X0 X0)) X1
       grind)
    | exact superpose eq6733 eq41346
    | exact resolve eq41346 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41346
  have eq41350 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq41348 X0 X1
       have i₂ := eq5868 X0 X0
       grind)
    | exact superpose eq5868 eq41348
    | exact resolve eq41348 eq5868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41348
  have eq41515 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op X0 (M.op X1 (M.op X1 X1))) (M.op X0 (M.op X1 (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq40673 X0 (M.op X1 (M.op X0 (M.op X0 X0)))
       have i₂ := eq41350 X0 X1
       grind)
    | exact superpose eq41350 eq40673
    | exact resolve eq40673 eq41350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41546 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X1 (M.op X0 X1)) (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq41515 X0 X1
       have i₂ := eq6733 (M.op X1 (M.op X1 X1)) X0
       grind)
    | exact superpose eq6733 eq41515
    | exact resolve eq41515 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41515
  have eq41633 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X1 (M.op X0 X1)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq41546 X0 X1
       have i₂ := eq5868 X1 X1
       grind)
    | exact superpose eq5868 eq41546
    | exact resolve eq41546 eq5868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5868 eq41546
  have eq41682 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq41633 X0 X1
       have i₂ := eq1971 (M.op X0 X1) X1
       grind)
    | exact superpose eq1971 eq41633
    | exact resolve eq41633 eq1971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41633
  have eq42220 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq41682 X0 X1
       have i₂ := eq6733 X1 X0
       grind)
    | exact superpose eq6733 eq41682
    | exact resolve eq41682 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41682
  have eq42762 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 (M.op X1 X0))) (M.op X1 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5789 X0 (M.op X1 X1)
       have i₂ := eq42220 X0 X1
       grind)
    | (have i₁ := eq5789 X1 (M.op X0 X1)
       have i₂ := eq42220 X0 X1
       grind)
    | exact superpose eq42220 eq5789
    | exact resolve eq5789 eq42220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43024 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq42762 X0 X1
       have i₂ := eq6733 (M.op X0 (M.op X1 X0)) X1
       grind)
    | exact superpose eq6733 eq42762
    | exact resolve eq42762 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42762
  have eq43272 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq43024 X0 X1
       have i₂ := eq6733 (M.op X1 X0) X0
       grind)
    | exact superpose eq6733 eq43024
    | exact resolve eq43024 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43024
  have eq43421 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq43272 X0 X1
       have i₂ := eq6733 X0 X1
       grind)
    | exact superpose eq6733 eq43272
    | exact resolve eq43272 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43272
  have eq50567 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 (M.op X0 (M.op X1 X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12760 X1 X0 X1
       have i₂ := eq42220 X0 X1
       grind)
    | (have i₁ := eq12760 X0 X1 X1
       have i₂ := eq42220 X0 X1
       grind)
    | exact superpose eq42220 eq12760
    | exact resolve eq12760 eq42220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12760
  have eq52266 : ∀ X0 X2 X3 : G, (M.op X3 X0) = (M.op X2 (M.op X2 (M.op (M.op X0 (M.op X0 X0)) (M.op X3 X0)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq601 X0 x X2 X3
       have i₂ := eq1971 X0 x
       grind)
    | exact superpose eq1971 eq601
    | exact resolve eq601 eq1971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq52450 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2))) (M.op (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2))) (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2))))) (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))) = (M.op X3 (M.op X3 (M.op X0 (M.op (M.op X1 X2) X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52266 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2))) X3 (M.op (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2))) (M.op (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2))) (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))))
       have i₂ := eq24 X2 (M.op (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2))) (M.op (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2))) (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2))))) X0 X1
       grind)
    | exact superpose eq24 eq52266
    | exact resolve eq52266 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52482 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2))) = (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op X0 (M.op (M.op X1 X2) X2)))) (M.op X0 (M.op (M.op X1 X2) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52266 (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op X0 (M.op (M.op X1 X2) X2)))) X2
       have i₂ := eq24 X2 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op X0 (M.op (M.op X1 X2) X2)))) X0 X1
       grind)
    | exact superpose eq24 eq52266
    | exact resolve eq52266 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq52492 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op X0 X1)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52266 (M.op X0 X1) (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op X1 (M.op X1 X1))
       have i₂ := eq52266 X1 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X0
       grind)
    | exact superpose eq52266 eq52266
    | exact resolve eq52266 eq52266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52266
  have eq52831 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52492 X0 X1
       have i₂ := eq1282 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq1282 eq52492
    | exact resolve eq52492 eq1282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52492
  have eq52840 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2))) = (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op X0 (M.op (M.op X1 X2) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52482 X0 X1 X2
       have i₂ := eq1282 (M.op X0 (M.op (M.op X1 X2) X2)) (M.op X0 (M.op (M.op X1 X2) X2))
       grind)
    | exact superpose eq1282 eq52482
    | exact resolve eq52482 eq1282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52482
  have eq52872 : ∀ X0 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X2 X2)))) = (M.op (M.op (M.op X2 (M.op X0 (M.op X2 X2))) (M.op (M.op X2 (M.op X0 (M.op X2 X2))) (M.op X2 (M.op X0 (M.op X2 X2))))) (M.op X2 (M.op X0 (M.op X2 X2)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq52450 X0 x X0 X3
       have i₂ := eq1971 X0 x
       grind)
    | exact superpose eq1971 eq52450
    | exact resolve eq52450 eq1971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52450
  have eq53080 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52831 X0 X1
       have i₂ := eq6733 X1 X0
       grind)
    | exact superpose eq6733 eq52831
    | exact resolve eq52831 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52831
  have eq53086 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2))) = (M.op X0 (M.op (M.op (M.op X1 X2) X2) (M.op (M.op X1 X2) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52840 X0 X1 X2
       have i₂ := eq6733 (M.op (M.op X1 X2) X2) X0
       grind)
    | exact superpose eq6733 eq52840
    | exact resolve eq52840 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52840
  have eq53116 : ∀ X0 X2 X3 : G, (M.op (M.op X2 (M.op X0 (M.op X2 X2))) (M.op X2 (M.op X0 (M.op X2 X2)))) = (M.op X3 (M.op X3 (M.op X0 (M.op X2 X2)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq52872 X0 X2 X3
       have i₂ := eq1282 (M.op X2 (M.op X0 (M.op X2 X2))) (M.op X2 (M.op X0 (M.op X2 X2)))
       grind)
    | exact superpose eq1282 eq52872
    | exact resolve eq52872 eq1282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282 eq52872
  have eq53240 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2))) = (M.op X0 (M.op (M.op X1 X2) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53086 X0 X1 X2
       have i₂ := eq6733 X2 (M.op X1 X2)
       grind)
    | exact superpose eq6733 eq53086
    | exact resolve eq53086 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53086
  have eq53264 : ∀ X0 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X2 X2)))) = (M.op X2 (M.op (M.op X0 (M.op X2 X2)) (M.op X0 (M.op X2 X2)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq53116 X0 X2 X3
       have i₂ := eq6733 (M.op X0 (M.op X2 X2)) X2
       grind)
    | exact superpose eq6733 eq53116
    | exact resolve eq53116 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53116
  have eq53328 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2))) = (M.op X0 (M.op X2 (M.op (M.op X1 X2) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53240 X0 X1 X2
       have i₂ := eq42220 (M.op X1 X2) X2
       grind)
    | exact superpose eq42220 eq53240
    | exact resolve eq53240 eq42220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53240
  have eq53341 : ∀ X0 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X2 X2)))) = (M.op X2 (M.op X0 (M.op (M.op X2 X2) (M.op X2 X2)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq53264 X0 X2 X3
       have i₂ := eq6733 (M.op X2 X2) X0
       grind)
    | exact superpose eq6733 eq53264
    | exact resolve eq53264 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53264
  have eq53382 : ∀ X0 X2 : G, (M.op X2 (M.op X0 (M.op X2 X2))) = (M.op X0 (M.op X2 (M.op X2 X2))) := by
    intro X0 X2
    first
    | (have i₁ := eq53328 X0 x X0
       have i₂ := eq1971 X0 x
       grind)
    | exact superpose eq1971 eq53328
    | exact resolve eq53328 eq1971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53328
  have eq53392 : ∀ X0 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X2 X2)))) = (M.op X2 (M.op X0 (M.op X2 (M.op (M.op X2 X2) X2)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq53341 X0 X2 X3
       have i₂ := eq42220 (M.op X2 X2) X2
       grind)
    | exact superpose eq42220 eq53341
    | exact resolve eq53341 eq42220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53341
  have eq53423 : ∀ X0 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X2 X2)))) = (M.op X2 (M.op X0 (M.op X2 (M.op X2 X2)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq53392 X0 X2 X3
       have i₂ := eq1252 X2
       grind)
    | exact superpose eq1252 eq53392
    | exact resolve eq53392 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53392
  have eq53447 : ∀ X0 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X2 X2)))) = (M.op X0 X2) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq53423 X0 X2 X3
       have i₂ := eq41350 X2 X0
       grind)
    | exact superpose eq41350 eq53423
    | exact resolve eq53423 eq41350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53423
  have eq53514 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X1 (M.op X1 (M.op X2 (σ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53447 X2 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq53447
    | exact resolve eq53447 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59318 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))) = (M.op (M.op X2 (M.op X1 X1)) (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3576 X0 X1 X2 X3
       have i₂ := eq42220 (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1))))
       grind)
    | exact superpose eq42220 eq3576
    | exact resolve eq3576 eq42220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3576
  have eq59319 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))) = (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op X1 (M.op X2 (M.op X1 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq59318 X0 X1 X2 X3
       have i₂ := eq6733 (M.op X1 (M.op X2 (M.op X1 X1))) X0
       grind)
    | exact superpose eq6733 eq59318
    | exact resolve eq59318 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59318
  have eq59320 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))) = (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X2 (M.op X1 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq59319 X0 X1 X2 X3
       have i₂ := eq2828 X2 X1
       grind)
    | exact superpose eq2828 eq59319
    | exact resolve eq59319 eq2828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59319
  have eq59321 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))) = (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op (M.op X2 (M.op X1 X1)) (M.op X2 (M.op X1 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq59320 X0 X1 X2 X3
       have i₂ := eq42220 X1 (M.op X2 (M.op X1 X1))
       grind)
    | exact superpose eq42220 eq59320
    | exact resolve eq59320 eq42220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59320
  have eq59322 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))) = (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op (M.op X1 X1) (M.op X1 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq59321 X0 X1 X2 X3
       have i₂ := eq6733 (M.op X1 X1) X2
       grind)
    | exact superpose eq6733 eq59321
    | exact resolve eq59321 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59321
  have eq59323 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))) = (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 (M.op (M.op X1 X1) X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq59322 X0 X1 X2 X3
       have i₂ := eq42220 (M.op X1 X1) X1
       grind)
    | exact superpose eq42220 eq59322
    | exact resolve eq59322 eq42220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59322
  have eq59324 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))) = (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq59323 X0 X1 X2 X3
       have i₂ := eq1252 X1
       grind)
    | exact superpose eq1252 eq59323
    | exact resolve eq59323 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59323
  have eq59325 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))) = (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X2 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq59324 X0 X1 X2 X3
       have i₂ := eq41350 X1 X2
       grind)
    | exact superpose eq41350 eq59324
    | exact resolve eq59324 eq41350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59324
  have eq59568 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 (M.op X3 (M.op (M.op (M.op X4 X1) X1) (M.op X1 (M.op (M.op (M.op X4 X1) X1) (M.op (M.op X4 X1) X1))))))) = (M.op (M.op X1 (M.op (M.op (M.op X4 X1) X1) (M.op (M.op X4 X1) X1))) (M.op X3 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq59325 X3 (M.op (M.op X4 X1) X1) X1 X2
       have i₂ := eq108 X1 X4 X0
       grind)
    | exact superpose eq108 eq59325
    | exact resolve eq59325 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq59325
  have eq60773 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 (M.op X3 (M.op (M.op (M.op X4 X1) X1) (M.op X1 (M.op (M.op X4 X1) (M.op X1 X1))))))) = (M.op (M.op X1 (M.op (M.op X4 X1) (M.op X1 X1))) (M.op X3 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq59568 X0 X0 X2 X3 X4
       have i₂ := eq6733 X0 (M.op X4 X0)
       grind)
    | exact superpose eq6733 eq59568
    | exact resolve eq59568 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59568
  have eq61395 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X3 (M.op X0 (M.op X0 X1)))) = (M.op X2 (M.op X2 (M.op X3 (M.op (M.op (M.op X4 X1) X1) X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq60773 X0 X0 X2 X3 X1
       have i₂ := eq2083 X0 X1
       grind)
    | exact superpose eq2083 eq60773
    | exact resolve eq60773 eq2083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60773
  have eq61822 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X3 (M.op X0 (M.op X0 X1)))) = (M.op X2 (M.op X2 (M.op X3 (M.op X1 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61395 X0 X1 X2 X3 x
       have i₂ := eq1971 X1 (M.op x X1)
       grind)
    | exact superpose eq1971 eq61395
    | exact resolve eq61395 eq1971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61395
  have eq62149 : ∀ X0 X1 X3 : G, (M.op X3 X1) = (M.op X1 (M.op X3 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq61822 X0 X1 x X3
       have i₂ := eq53447 X3 X1 x
       grind)
    | exact superpose eq53447 eq61822
    | exact resolve eq61822 eq53447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53447 eq61822
  have eq68103 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X1 (M.op X1 X0)) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43421 (M.op X0 (M.op X0 X1)) X1
       have i₂ := eq5789 X0 X1
       grind)
    | exact superpose eq5789 eq43421
    | exact resolve eq43421 eq5789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5789 eq43421
  have eq86816 : ∀ X0 X2 X3 : G, (M.op X3 (M.op X3 (M.op X2 X0))) = (M.op (M.op X2 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq571 X0 x X2 X3
       have i₂ := eq1971 X0 x
       grind)
    | exact superpose eq1971 eq571
    | exact resolve eq571 eq1971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571 eq1971
  have eq87112 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) = (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op (M.op X1 X1) (M.op (M.op X1 X1) (M.op X1 X1))) (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq86816 (M.op X1 X1) (M.op X0 (M.op X0 X1)) x
       have i₂ := eq40673 X0 X1
       grind)
    | exact superpose eq40673 eq86816
    | exact resolve eq86816 eq40673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40673 eq86816
  have eq87734 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X1 (M.op X0 (M.op X0 X1)))) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87112 X0 X1 X2
       have i₂ := eq1283 X1 (M.op X1 X1)
       grind)
    | exact superpose eq1283 eq87112
    | exact resolve eq87112 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87112
  have eq88153 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) = (M.op X1 (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87734 X0 X1 X2
       have i₂ := eq42220 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq42220 eq87734
    | exact resolve eq87734 eq42220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87734
  have eq88454 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq88153 X0 X1 X2
       have i₂ := eq62149 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq62149 eq88153
    | exact resolve eq88153 eq62149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62149 eq88153
  have eq212170 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X4 (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))))) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))) (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2438 X0 X1 X2 X3 X4
       have i₂ := eq42220 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1))))))
       grind)
    | exact superpose eq42220 eq2438
    | exact resolve eq2438 eq42220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2438
  have eq212171 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X4 (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))))) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op X3 (M.op (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1))))) (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq212170 X0 X1 X2 X3 X4
       have i₂ := eq6733 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1))))) X3
       grind)
    | exact superpose eq6733 eq212170
    | exact resolve eq212170 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212170
  have eq212172 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X4 (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))))) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq212171 X0 X1 X2 X3 X4
       have i₂ := eq6733 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op X2 (M.op X1 X1))
       grind)
    | exact superpose eq6733 eq212171
    | exact resolve eq212171 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212171
  have eq212173 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X4 (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))))) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op X1 (M.op X2 (M.op X1 X1)))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq212172 X0 X1 X2 X3 X4
       have i₂ := eq6733 (M.op X1 (M.op X2 (M.op X1 X1))) X0
       grind)
    | exact superpose eq6733 eq212172
    | exact resolve eq212172 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212172
  have eq212174 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X4 (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))))) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X2 (M.op X1 X1)))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq212173 X0 X1 X2 X3 X4
       have i₂ := eq2828 X2 X1
       grind)
    | exact superpose eq2828 eq212173
    | exact resolve eq212173 eq2828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2828 eq212173
  have eq212175 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X4 (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))))) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op (M.op X2 (M.op X1 X1)) (M.op X2 (M.op X1 X1)))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq212174 X0 X1 X2 X3 X4
       have i₂ := eq42220 X1 (M.op X2 (M.op X1 X1))
       grind)
    | exact superpose eq42220 eq212174
    | exact resolve eq212174 eq42220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212174
  have eq212176 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X4 (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))))) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op (M.op X1 X1) (M.op X1 X1)))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq212175 X0 X1 X2 X3 X4
       have i₂ := eq6733 (M.op X1 X1) X2
       grind)
    | exact superpose eq6733 eq212175
    | exact resolve eq212175 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212175
  have eq212177 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X4 (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))))) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 (M.op (M.op X1 X1) X1)))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq212176 X0 X1 X2 X3 X4
       have i₂ := eq42220 (M.op X1 X1) X1
       grind)
    | exact superpose eq42220 eq212176
    | exact resolve eq212176 eq42220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212176
  have eq212178 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X4 (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))))) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 (M.op X1 X1)))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq212177 X0 X1 X2 X3 X4
       have i₂ := eq1252 X1
       grind)
    | exact superpose eq1252 eq212177
    | exact resolve eq212177 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212177
  have eq212179 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X4 (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))))))) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op X3 (M.op (M.op X2 (M.op X1 X1)) (M.op X0 (M.op X2 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq212178 X0 X1 X2 X3 X4
       have i₂ := eq41350 X1 X2
       grind)
    | exact superpose eq41350 eq212178
    | exact resolve eq212178 eq41350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41350 eq212178
  have eq212912 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 (M.op X2 (M.op (M.op X0 (M.op (M.op (M.op X3 X0) X0) (M.op (M.op X3 X0) X0))) (M.op (M.op (M.op X3 X0) X0) (M.op (M.op (M.op X3 X0) X0) (M.op X0 (M.op (M.op (M.op X3 X0) X0) (M.op (M.op X3 X0) X0))))))))) = (M.op (M.op (M.op (M.op X3 X0) X0) (M.op (M.op (M.op X3 X0) X0) (M.op X0 (M.op (M.op (M.op X3 X0) X0) (M.op (M.op X3 X0) X0))))) (M.op X2 (M.op (M.op X0 (M.op (M.op (M.op X3 X0) X0) (M.op (M.op X3 X0) X0))) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq212179 (M.op (M.op X3 X0) X0) (M.op (M.op X3 X0) X0) X0 X2 X1
       have i₂ := eq1937 X3 X0
       grind)
    | exact superpose eq1937 eq212179
    | exact resolve eq212179 eq1937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1937 eq212179
  have eq214076 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 (M.op X2 (M.op (M.op X0 (M.op (M.op X3 X0) (M.op X0 X0))) (M.op (M.op (M.op X3 X0) X0) (M.op (M.op (M.op X3 X0) X0) (M.op X0 (M.op (M.op X3 X0) (M.op X0 X0))))))))) = (M.op (M.op (M.op (M.op X3 X0) X0) (M.op (M.op (M.op X3 X0) X0) (M.op X0 (M.op (M.op X3 X0) (M.op X0 X0))))) (M.op X2 (M.op (M.op X0 (M.op (M.op X3 X0) (M.op X0 X0))) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq212912 X0 X1 X2 X3
       have i₂ := eq6733 X0 (M.op X3 X0)
       grind)
    | exact superpose eq6733 eq212912
    | exact resolve eq212912 eq6733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6733 eq212912
  have eq215149 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 (M.op X2 (M.op (M.op X0 (M.op (M.op X3 X0) (M.op X0 X0))) (M.op (M.op (M.op X3 X0) X0) (M.op (M.op (M.op X3 X0) X0) (M.op X0 (M.op (M.op X3 X0) (M.op X0 X0))))))))) = (M.op (M.op (M.op (M.op X3 X0) X0) (M.op (M.op (M.op X3 X0) X0) (M.op X0 (M.op (M.op X3 X0) (M.op X0 X0))))) (M.op X2 (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq214076 X0 X1 X2 X3
       have i₂ := eq50567 (M.op X3 X0) X0
       grind)
    | exact superpose eq50567 eq214076
    | exact resolve eq214076 eq50567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50567 eq214076
  have eq216092 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 (M.op X2 (M.op X0 (M.op (M.op (M.op X3 X0) X0) (M.op (M.op (M.op X3 X0) X0) X0)))))) = (M.op (M.op (M.op (M.op X3 X0) X0) (M.op (M.op (M.op X3 X0) X0) X0)) (M.op X2 (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq215149 X0 X1 X2 X1
       have i₂ := eq2083 X0 X1
       grind)
    | exact superpose eq2083 eq215149
    | exact resolve eq215149 eq2083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2083 eq215149
  have eq216895 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X2 (M.op X0 X0))) = (M.op X1 (M.op X1 (M.op X2 (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq216092 X0 X1 X2 x
       have i₂ := eq4055 X0 (M.op (M.op x X0) X0)
       grind)
    | exact superpose eq4055 eq216092
    | exact resolve eq216092 eq4055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216092
  have eq217576 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X2 X0))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X2 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq216895 X0 X1 X2
       have i₂ := eq1291 X0
       grind)
    | exact superpose eq1291 eq216895
    | exact resolve eq216895 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291 eq216895
  have eq218157 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X1 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq217576 X0 X1 X2
       have i₂ := eq12887 (M.op X0 X0) X2
       grind)
    | exact superpose eq12887 eq217576
    | exact resolve eq217576 eq12887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12887 eq217576
  have eq218638 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X2 X0))) = (M.op X2 (M.op X0 (M.op (M.op X0 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq218157 X0 X1 X2
       have i₂ := eq42220 (M.op X0 X0) X0
       grind)
    | exact superpose eq42220 eq218157
    | exact resolve eq218157 eq42220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42220 eq218157
  have eq219030 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X0 X0))) = (M.op X1 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq218638 X0 X1 X2
       have i₂ := eq1252 X0
       grind)
    | exact superpose eq1252 eq218638
    | exact resolve eq218638 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252 eq218638
  have eq533492 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X0 X1))) (M.op X2 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53080 X0 (M.op X0 X0)
       have i₂ := eq4055 X0 X2
       grind)
    | exact superpose eq4055 eq53080
    | exact resolve eq53080 eq4055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4055 eq53080
  have eq535617 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op X1 (M.op X2 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq533492 X0 X1 X2
       have i₂ := eq1268 X1 X0 X1
       grind)
    | exact superpose eq1268 eq533492
    | exact resolve eq533492 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268 eq533492
  have eq597059 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))))) = (M.op (M.op X1 (M.op X1 X2)) (M.op X2 (M.op X2 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq219030 X2 X3 (M.op X1 (M.op X1 X2))
       have i₂ := eq88454 X1 X2 X0
       grind)
    | exact superpose eq88454 eq219030
    | exact resolve eq219030 eq88454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88454 eq219030
  have eq598968 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))))) = (M.op X2 (M.op (M.op X1 (M.op X1 X2)) (M.op X2 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq597059 X0 X1 X2 X3
       have i₂ := eq53382 (M.op X1 (M.op X1 X2)) X2
       grind)
    | exact superpose eq53382 eq597059
    | exact resolve eq597059 eq53382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53382 eq597059
  have eq600123 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq598968 X0 X1 X2 X3
       have i₂ := eq68103 X2 X1 X2
       grind)
    | exact superpose eq68103 eq598968
    | exact resolve eq598968 eq68103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598968
  have eq935856 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op X0 (M.op X1 (M.op X1 (M.op (σ y) (σ (M.op y y))))))) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq600123 X1 (σ y) (σ x) X0
       have i₂ := eq14952
       grind)
    | exact superpose eq14952 eq600123
    | exact resolve eq600123 eq14952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14952 eq600123
  have eq935880 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (M.op (σ y) (σ y)))) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq935856 X0 x
       have i₂ := eq53514 y x (σ y)
       grind)
    | exact superpose eq53514 eq935856
    | exact resolve eq935856 eq53514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53514 eq935856
  have eq936033 : (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq935880 x
       have i₂ := eq1283 (σ y) x
       grind)
    | exact superpose eq1283 eq935880
    | exact resolve eq935880 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283 eq935880
  have eq936034 : (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq936033
  have eq936543 : y = (M.op (M.op y (M.op y x)) (M.op y (M.op y x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq7266 y y
       have i₂ := eq936034
       grind)
    | exact superpose eq936034 eq7266
    | exact resolve eq7266 eq936034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7266 eq936034
  have eq936720 : y = (M.op x (M.op (M.op y (M.op y x)) (M.op x x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq936543
       have i₂ := eq535617 y x (M.op y (M.op y x))
       grind)
    | exact superpose eq535617 eq936543
    | exact resolve eq936543 eq535617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535617 eq936543
  have eq936858 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq936720
       have i₂ := eq68103 x y x
       grind)
    | exact superpose eq68103 eq936720
    | exact resolve eq936720 eq68103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68103 eq936720
  have eq936942 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq936858
       grind)
    | exact superpose eq936858 eq16
    | exact resolve eq16 eq936858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936858
  have eq936943 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq936942
       have r₂ := eq22 x
       grind)
    | exact resolve eq936942 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936942
  have eq936945 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq936943
       grind)
    | exact superpose eq936943 eq10
    | exact resolve eq10 eq936943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936943
  have eq937458 : x = y := by
    first
    | (have i₁ := eq936945
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq936945
    | exact resolve eq936945 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936945
  have eq937471 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq937458
       grind)
    | exact superpose eq937458 eq16
    | exact resolve eq16 eq937458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937458
  have eq937472 : False := by grind
  exact eq937472

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq42 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq56
    | exact resolve eq56 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq56
  have eq79 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq79 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq79
    | (have j0 := eq79 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq79 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80 y x
       grind)
    | exact superpose eq80 eq16
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq260 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq187
       have i₂ := eq79 y x
       grind)
    | exact superpose eq79 eq187
    | (have j1 := eq79 (σ x) (σ y)
       grind)
    | (have r₁ := eq187
       have r₂ := eq79 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq187
       have r₂ := eq79 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq187 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq187
  have eq263 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq260
  have eq264 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq263
       grind)
    | exact superpose eq263 eq16
    | exact resolve eq16 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq265 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq264
       have r₂ := eq65 x
       grind)
    | exact resolve eq264 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq301 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq265
       grind)
    | exact superpose eq265 eq10
    | exact resolve eq10 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq318 : x = y := by
    first
    | (have i₁ := eq301
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq301
    | exact resolve eq301 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq362 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq318
       grind)
    | exact superpose eq318 eq16
    | exact resolve eq16 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq363 : False := by grind
  exact eq363

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxx_pxy_Equation837 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  clear eq37
  have eq76 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq78 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq45
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq103
    | exact resolve eq103 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq109
    | exact resolve eq109 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq406 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq76 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq7560 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq110 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7561 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq7560
    | exact resolve eq7560 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7560
  have eq7572 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq7561
       have r₂ := eq29
       grind)
    | exact resolve eq7561 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7561
  have eq7582 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq7572
  have eq7602 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq7582
    | exact resolve eq7582 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7582
  have eq7644 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq7602 eq110
    | exact resolve eq110 eq7602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq7602
  have eq7653 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq7644
  have eq7656 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7653
       have r₂ := eq29
       grind)
    | exact resolve eq7653 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7653
  have eq7667 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq7656
  have eq7688 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq7667
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq7667
    | exact resolve eq7667 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7667
  have eq7727 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq7688
       grind)
    | exact superpose eq7688 eq46
    | exact resolve eq46 eq7688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq7688
  have eq7743 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22 eq7727
    | exact resolve eq7727 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7727
  have eq7909 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7743 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq7743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7910 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq7909
  have eq7914 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq7910
    | exact resolve eq7910 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7910
  have eq7925 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq7914
       have r₂ := eq29
       grind)
    | exact resolve eq7914 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7914
  have eq8103 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7925
  have eq8123 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq8103
    | exact resolve eq8103 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8103
  have eq8347 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8123 eq7743
    | exact resolve eq7743 eq8123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7743 eq8123
  have eq8350 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq8347
  have eq8355 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq8350
       have r₂ := eq29
       grind)
    | exact resolve eq8350 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8350
  have eq8524 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq8355 eq31
    | exact resolve eq31 eq8355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq8355
  have eq8643 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq8524
    | exact resolve eq8524 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq8524
  have eq8644 : x = y := by grind
  clear eq8643
  have eq8645 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq8644
       grind)
    | exact superpose eq8644 eq20
    | exact resolve eq20 eq8644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq8646 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq8644
       grind)
    | exact superpose eq8644 eq26
    | exact resolve eq26 eq8644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq8644
  have eq8755 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq8646
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8646
    | exact resolve eq8646 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8646
  have eq8756 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq8755 eq28
    | exact resolve eq28 eq8755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq8755
  have eq9194 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq8645
       grind)
    | exact superpose eq8645 eq78
    | exact resolve eq78 eq8645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq9209 : (k (M.op x y) x) = (M.op (M.op x y) x) := by grind
  have eq9226 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22 eq9194
    | exact resolve eq9194 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9194
  have eq9241 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq10063 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq10071 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8756 eq10063
    | exact resolve eq10063 eq8756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10063
  have eq10083 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10071
       have r₂ := eq29
       grind)
    | exact resolve eq10071 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10071
  have eq10088 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8756 eq10083
    | exact resolve eq10083 eq8756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10083
  have eq10117 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10088 eq9241
    | exact resolve eq9241 eq10088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9241 eq10088
  have eq10119 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8756 eq10117
    | exact resolve eq10117 eq8756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10117
  have eq12994 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10119 eq9226
    | exact resolve eq9226 eq10119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9226 eq10119
  have eq13002 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12994
  have eq13006 : x = (M.op x y) := by
    first
    | (have r₁ := eq13002
       have r₂ := eq29
       grind)
    | exact resolve eq13002 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13002
  have eq13017 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq13006 eq22
    | exact resolve eq22 eq13006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq13090 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq13006 eq9209
    | exact resolve eq9209 eq13006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9209
  have eq13094 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq13090
       have i₂ := eq8645
       grind)
    | exact superpose eq8645 eq13090
    | exact resolve eq13090 eq8645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8645 eq13090
  have eq13155 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13017
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13017
    | exact resolve eq13017 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13017
  have eq13157 : x = (k x x) := by
    first
    | exact superpose eq13006 eq13094
    | exact resolve eq13094 eq13006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13006 eq13094
  have eq16524 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq406 x
       have i₂ := eq13157
       grind)
    | exact superpose eq13157 eq406
    | (have j0 := eq406 x
       grind)
    | exact resolve eq406 eq13157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq13157
  have eq16528 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq16524
  have eq16534 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16528
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16528
    | exact resolve eq16528 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq16528
  have eq16546 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8756 eq16534
    | exact resolve eq16534 eq8756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8756 eq16534
  have eq16556 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13155 eq16546
    | exact resolve eq16546 eq13155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13155 eq16546
  have eq16565 : False := by grind
  exact eq16565

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pyx_pxx_pyx_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = (M.op X0 X0) := by
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
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq33 (σ X0)
       grind)
    | exact superpose eq33 eq15
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq33 (τ X0)
       grind)
    | exact superpose eq33 eq19
    | exact resolve eq19 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq38 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq35
    | exact resolve eq35 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq38
    | exact resolve eq38 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq38
  have eq57 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq62 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq64 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq62
    | (have j0 := eq62 X0 X1
       grind)
    | exact resolve eq62 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq88 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq64
    | (have j0 := eq64 (τ X0) X1
       grind)
    | exact resolve eq64 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq140 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq132 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq132
    | (have j0 := eq132 X0 X1
       grind)
    | exact resolve eq132 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq146 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq140 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq140
    | (have j0 := eq140 X0 X1
       grind)
    | exact resolve eq140 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq140
  have eq150 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq146 X0 X1
       have j1 := eq88 X1 X0
       grind)
    | (have r₁ := eq146 X1 X0
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq146 (M.op X1 X1) (M.op X0 X0)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq146 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq146
  have eq174 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq150 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq150
    | exact resolve eq150 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq150 (σ X1) X0
       grind)
    | exact superpose eq150 eq15
    | (have j1 := eq150 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq188 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq174 X0 (τ X1)
       grind)
    | exact superpose eq174 eq18
    | (have j1 := eq174 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq174
  have eq465 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq188 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq188
    | exact resolve eq188 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq497 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq465 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq465
    | (have j0 := eq465 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq465 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq1182 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq179 x y
       grind)
    | exact superpose eq179 eq16
    | (have j1 := eq179 x y
       grind)
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq1197 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1182
       have i₂ := eq497 y x
       grind)
    | exact superpose eq497 eq1182
    | (have j1 := eq497 (σ x) (σ y)
       grind)
    | (have r₁ := eq1182
       have r₂ := eq497 y x
       grind)
    | (have r₁ := eq1182
       have r₂ := eq497 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1182
       have r₂ := eq497 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1182 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497 eq1182
  have eq1198 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1197
  have eq1294 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1198
       grind)
    | exact superpose eq1198 eq10
    | exact resolve eq10 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq1338 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1294
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1294
    | exact resolve eq1294 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294
  have eq1339 : x = y := by grind
  clear eq1338
  have eq1341 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1339
       grind)
    | exact superpose eq1339 eq16
    | exact resolve eq16 eq1339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339
  have eq1342 : False := by grind
  exact eq1342

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_pyy_pyx_pyy_pyx_Equation842 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq89 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X2 X0) ∨ (M.op X0 X2) = X2 ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X2 X0) ∨ (M.op X0 X2) = X2 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq89 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq89 X1 (k X2 X1) X2
       have r₂ := eq12 (k X2 X1) X1
       grind)
    | (have r₁ := eq89 X1 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq89 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq89 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq1391 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq1392 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1391 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391
  have eq1393 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1392 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1392 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1392 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392
  have eq1422 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1393 (σ X0) (σ X1)
       grind)
    | exact superpose eq1393 eq15
    | exact resolve eq15 eq1393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1449 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1422 X0 X1
       have i₂ := eq1393 X0 X1
       grind)
    | exact superpose eq1393 eq1422
    | exact resolve eq1422 eq1393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393 eq1422
  have eq1717 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1449 x y
       grind)
    | exact superpose eq1449 eq16
    | (have r₁ := eq16
       have r₂ := eq1449 x y
       grind)
    | exact resolve eq16 eq1449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449
  have eq1773 : False := by grind
  exact eq1773

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pyx_pxy_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
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
  have eq51 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (k (M.op X1 X2) X0) ∨ (M.op X0 X0) = (M.op X1 X2) ∨ (M.op X1 (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1
       have i₂ := eq11 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq14 X0 X1
       have i₂ := eq11 X0 (M.op X1 X0)
       grind)
    | exact superpose eq11 eq14
    | (have j1 := eq11 (M.op X1 X2) X0
       grind)
    | exact resolve eq14 eq11
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
  clear eq37
  have eq97 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X2 ∨ (k X2 X1) = (M.op X2 X1) ∨ (M.op X2 X2) = X0 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq11 X0 X2
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq11 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 (M.op X0 X0) X1
       grind)
    | exact resolve eq12 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq137 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq119 eq16
    | exact resolve eq16 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq268 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq98 x
       grind)
    | exact superpose eq98 eq44
    | (have j1 := eq98 x
       grind)
    | exact resolve eq44 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq271 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq137
       have i₂ := eq98 sF1
       grind)
    | exact superpose eq98 eq137
    | (have j1 := eq98 (σ (M.op x y))
       grind)
    | exact resolve eq137 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq137
  have eq298 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq307 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (k (M.op X0 (M.op X1 X1)) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq314 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq308 X0 X1
       have i₂ := eq53 (M.op X1 X1) X0
       grind)
    | exact superpose eq53 eq308
    | exact resolve eq308 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq320 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq298 X0 X1
       have i₂ := eq53 (M.op X1 X1) X0
       grind)
    | exact superpose eq53 eq298
    | exact resolve eq298 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq324 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq314 X0 X1
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq314
    | exact resolve eq314 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq327 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq320 X0 X1
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq320
    | exact resolve eq320 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq332 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq307 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq307 (M.op X0 X0) X0
       grind)
    | exact superpose eq307 eq307
    | exact resolve eq307 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq852 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op x (M.op X0 X0)) ∨ (M.op X0 X0) = y ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq51 eq77
    | (have j0 := eq77 (M.op x y) x (M.op X0 X0)
       grind)
    | exact resolve eq77 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq858 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 X0)) ∨ (M.op X0 X0) = (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq52 eq77
    | (have j0 := eq77 (M.op (σ x) (σ y)) (σ x) (M.op X0 X0)
       grind)
    | exact resolve eq77 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1866 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq97 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq4464 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq324 X1 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq324
    | exact resolve eq324 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq4556 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4464 X0 X1
       have i₂ := eq307 (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq307 eq4464
    | exact resolve eq4464 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4464
  have eq6862 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 X1)) (M.op X0 X1)) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq313 X0 X1
       have i₂ := eq327 X0 X1
       grind)
    | exact superpose eq327 eq313
    | exact resolve eq313 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq327
  have eq6873 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq6862 (M.op x x) (M.op x x)
       have i₂ := eq307 (M.op x x) x
       grind)
    | exact superpose eq307 eq6862
    | exact resolve eq6862 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307 eq6862
  have eq7040 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq6873 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq6873
    | exact resolve eq6873 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq6873
  have eq7111 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq7040 X0
       have i₂ := eq332 X0
       grind)
    | exact superpose eq332 eq7040
    | exact resolve eq7040 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332 eq7040
  have eq8423 : x = (M.op x (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq4556 x x
       have i₂ := eq852 x
       grind)
    | exact superpose eq852 eq4556
    | (have j1 := eq852 x
       grind)
    | exact resolve eq4556 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq8463 : x = y ∨ y = (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq51 eq8423
    | exact resolve eq8423 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq8423
  have eq8488 : (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8463
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8463
    | exact resolve eq8463 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8463
  have eq8782 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq858 eq4556
    | (have j1 := eq858 (σ x)
       grind)
    | exact resolve eq4556 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858 eq4556
  have eq8826 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq52 eq8782
    | exact resolve eq8782 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq8782
  have eq8853 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq8826
    | exact resolve eq8826 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8826
  have eq32169 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq86
       have i₂ := eq8488
       grind)
    | exact superpose eq8488 eq86
    | exact resolve eq86 eq8488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8488
  have eq32207 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq32169
    | exact resolve eq32169 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32169
  have eq36678 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq32207 eq8853
    | exact resolve eq8853 eq32207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36695 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq36678
       have r₂ := eq28
       grind)
    | exact resolve eq36678 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36678
  have eq36931 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq36695
  have eq37086 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq36931
    | exact resolve eq36931 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36931
  have eq38301 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq37086 eq32207
    | exact resolve eq32207 eq37086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32207 eq37086
  have eq38311 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq38301
  have eq38313 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq38311
       have r₂ := eq28
       grind)
    | exact resolve eq38311 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38311
  have eq38527 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq38313
  have eq38690 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq38527
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq38527
    | exact resolve eq38527 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38527
  have eq40021 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq38690
       grind)
    | exact superpose eq38690 eq86
    | exact resolve eq86 eq38690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq38690
  have eq40047 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq40021
    | exact resolve eq40021 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40021
  have eq40809 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq40047 eq8853
    | exact resolve eq8853 eq40047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8853
  have eq40821 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq40809
  have eq40831 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq40821
       have r₂ := eq28
       grind)
    | exact resolve eq40821 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40821
  have eq40912 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq40831
  have eq41076 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq40912
    | exact resolve eq40912 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40912
  have eq42455 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq41076 eq40047
    | exact resolve eq40047 eq41076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40047 eq41076
  have eq42465 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq42455
  have eq42469 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq42465
       have r₂ := eq28
       grind)
    | exact resolve eq42465 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42465
  have eq42558 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq42469 eq30
    | exact resolve eq30 eq42469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq42469
  have eq42688 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq42558
    | exact resolve eq42558 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq42558
  have eq42689 : x = y := by grind
  clear eq42688
  have eq42690 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq42689
       grind)
    | exact superpose eq42689 eq19
    | exact resolve eq19 eq42689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq42691 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq42689
       grind)
    | exact superpose eq42689 eq25
    | exact resolve eq25 eq42689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq42689
  have eq42824 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq42691
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq42691
    | exact resolve eq42691 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42691
  have eq42825 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq42824 eq27
    | exact resolve eq27 eq42824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq42824
  have eq43054 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq268
       have i₂ := eq42690
       grind)
    | exact superpose eq42690 eq268
    | exact resolve eq268 eq42690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq43145 : (M.op x y) = (k x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq7111 x
       have i₂ := eq42690
       grind)
    | exact superpose eq42690 eq7111
    | exact resolve eq7111 eq42690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7111
  have eq43187 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq43054
    | exact resolve eq43054 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43054
  have eq43211 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq50299 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43187 eq1866
    | (have j0 := eq1866 (σ x) (σ x)
       grind)
    | exact resolve eq1866 eq43187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1866
  have eq50300 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq50299
  have eq50307 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42825 eq50300
    | exact resolve eq50300 eq42825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50300
  have eq50326 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq50307
       have r₂ := eq28
       grind)
    | exact resolve eq50307 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50307
  have eq50334 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42825 eq50326
    | exact resolve eq50326 eq42825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50326
  have eq50371 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50334 eq43211
    | exact resolve eq43211 eq50334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43211 eq50334
  have eq50383 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42825 eq50371
    | exact resolve eq50371 eq42825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50371
  have eq51216 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50383 eq43187
    | exact resolve eq43187 eq50383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43187 eq50383
  have eq51229 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq51216
  have eq51234 : x = (M.op x y) := by
    first
    | (have r₁ := eq51229
       have r₂ := eq28
       grind)
    | exact resolve eq51229 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51229
  have eq51242 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq51234 eq21
    | exact resolve eq21 eq51234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq51333 : x = (k x (M.op x x)) := by
    first
    | exact superpose eq51234 eq43145
    | exact resolve eq43145 eq51234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43145
  have eq51338 : x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq51333
       have i₂ := eq42690
       grind)
    | exact superpose eq42690 eq51333
    | exact resolve eq51333 eq42690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42690 eq51333
  have eq51418 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq51242
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq51242
    | exact resolve eq51242 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51242
  have eq51421 : x = (k x x) := by
    first
    | exact superpose eq51234 eq51338
    | exact resolve eq51338 eq51234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51338
  have eq51637 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq51418 eq42825
    | exact resolve eq42825 eq51418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42825
  have eq52003 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51637 eq271
    | exact resolve eq271 eq51637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq51637
  have eq52172 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq52003
       have r₂ := eq28
       grind)
    | exact resolve eq52003 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52003
  have eq52186 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq51234 eq52172
    | exact resolve eq52172 eq51234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51234 eq52172
  have eq52195 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq52186
       have i₂ := eq51421
       grind)
    | exact superpose eq51421 eq52186
    | exact resolve eq52186 eq51421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51421 eq52186
  have eq52223 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq52195 eq15
    | exact resolve eq15 eq52195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52195
  have eq52329 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52223
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq52223
    | exact resolve eq52223 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq52223
  have eq52374 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51418 eq52329
    | exact resolve eq52329 eq51418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51418 eq52329
  have eq52406 : False := by grind
  exact eq52406
