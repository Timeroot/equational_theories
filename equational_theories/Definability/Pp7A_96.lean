import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_pxy_pxx_pxy_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq265 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq265 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq265 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq265 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq277 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq266 (σ X0)
       grind)
    | exact superpose eq266 eq15
    | exact resolve eq15 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq266 (τ X0)
       grind)
    | exact superpose eq266 eq31
    | exact resolve eq31 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq283 X0
       have i₂ := eq266 X0
       grind)
    | exact superpose eq266 eq283
    | exact resolve eq283 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq296 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq277 X0
       have i₂ := eq266 X0
       grind)
    | exact superpose eq266 eq277
    | exact resolve eq277 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq277
  have eq338 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq296 X0
       grind)
    | exact superpose eq296 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq475 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq498 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq475 X0 X1
       have i₂ := eq296 X0
       grind)
    | exact superpose eq296 eq475
    | (have j0 := eq475 X0 X1
       grind)
    | exact resolve eq475 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq738 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq498 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq498
    | exact resolve eq498 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq776 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq738 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq738
    | (have j0 := eq738 X0 X1
       grind)
    | exact resolve eq738 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq738
  have eq778 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq776 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq776 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq776 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq779 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq778 X0 X1
       have i₂ := eq290 X0
       grind)
    | exact superpose eq290 eq778
    | (have j0 := eq778 X0 X1
       grind)
    | exact resolve eq778 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq780 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq779 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq779
    | (have j0 := eq779 X0 X1
       grind)
    | exact resolve eq779 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq781 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq780 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq780
    | exact resolve eq780 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq780 (σ X0) X1
       grind)
    | exact superpose eq780 eq15
    | (have j1 := eq780 (σ X0) X1
       grind)
    | exact resolve eq15 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq819 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq794 X0 X1
       have i₂ := eq296 X0
       grind)
    | exact superpose eq296 eq794
    | (have j0 := eq794 X0 X1
       grind)
    | exact resolve eq794 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296 eq794
  have eq838 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq781 (τ X1) X0
       grind)
    | exact superpose eq781 eq18
    | (have j1 := eq781 (τ X1) X0
       grind)
    | exact resolve eq18 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq781
  have eq989 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq838 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq838
    | exact resolve eq838 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq1031 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq989 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq989
    | (have j0 := eq989 X0 X1
       grind)
    | exact resolve eq989 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq2622 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq819 x y
       grind)
    | exact superpose eq819 eq16
    | (have j1 := eq819 x y
       grind)
    | exact resolve eq16 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2641 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq819 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq2670 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2622
       have i₂ := eq1031 y x
       grind)
    | exact superpose eq1031 eq2622
    | (have j1 := eq1031 y x
       grind)
    | (have r₁ := eq2622
       have r₂ := eq1031 y x
       grind)
    | exact resolve eq2622 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031 eq2622
  have eq2671 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2670
  have eq2674 : (M.op x x) ≠ (M.op x x) ∨ y = (M.op y x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2671
       grind)
    | exact superpose eq2671 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2671
       grind)
    | exact resolve eq13 eq2671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2676 : y = (M.op y x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2674
  have eq2685 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2641 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq2641
    | (have j0 := eq2641 (τ X0) (τ X1)
       grind)
    | exact resolve eq2641 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2730 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (τ (M.op X0 X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2685 X0 X1
       have i₂ := eq290 X0
       grind)
    | exact superpose eq290 eq2685
    | (have j0 := eq2685 X0 X1
       grind)
    | exact resolve eq2685 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2685
  have eq2750 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2730 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq2730
    | (have j0 := eq2730 X0 X1
       grind)
    | exact resolve eq2730 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2730
  have eq2766 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2750 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2750
    | (have j0 := eq2750 X0 X1
       grind)
    | exact resolve eq2750 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2750
  have eq2778 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2766 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2766
    | (have j0 := eq2766 X0 X1
       grind)
    | exact resolve eq2766 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2766
  have eq2785 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2778 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2778
    | (have j0 := eq2778 X0 X1
       grind)
    | exact resolve eq2778 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2778
  have eq2790 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2785 X0 X1
       have i₂ := eq290 X0
       grind)
    | exact superpose eq290 eq2785
    | (have j0 := eq2785 X0 X1
       grind)
    | exact resolve eq2785 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290 eq2785
  have eq2791 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2790 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq2790
    | (have j0 := eq2790 X0 X1
       grind)
    | exact resolve eq2790 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2790
  have eq10330 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq2676
       grind)
    | exact superpose eq2676 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq2676
       grind)
    | exact resolve eq12 eq2676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2676
  have eq10331 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
  clear eq10330
  have eq67671 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10331
       grind)
    | exact superpose eq10331 eq16
    | exact resolve eq16 eq10331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10331
  have eq67718 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq67671
       have i₂ := eq2671
       grind)
    | exact superpose eq2671 eq67671
    | exact resolve eq67671 eq2671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2671 eq67671
  have eq67719 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq67718
  have eq67720 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by grind
  clear eq67719
  have eq67724 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq338 x (σ y)
       have i₂ := eq67720
       grind)
    | exact superpose eq67720 eq338
    | (have j0 := eq338 x (σ y)
       grind)
    | (have r₁ := eq338 x (σ y)
       have r₂ := eq67720
       grind)
    | exact resolve eq338 eq67720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq67751 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by grind
  clear eq67724
  have eq67761 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq67751
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq67751
    | exact resolve eq67751 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67751
  have eq108794 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq67761
       grind)
    | exact superpose eq67761 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq67761
       grind)
    | exact resolve eq12 eq67761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67761
  have eq108811 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by grind
  clear eq108794
  have eq108828 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq108811
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq108811
    | exact resolve eq108811 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108811
  have eq962257 : (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq67720
       have i₂ := eq108828
       grind)
    | exact superpose eq108828 eq67720
    | exact resolve eq67720 eq108828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67720 eq108828
  have eq962451 : (k x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq962257
  have eq962612 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2641 x y
       have i₂ := eq962451
       grind)
    | exact superpose eq962451 eq2641
    | (have j0 := eq2641 x y
       grind)
    | (have r₁ := eq2641 x y
       have r₂ := eq962451
       grind)
    | exact resolve eq2641 eq962451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq962614 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2791 x y
       have i₂ := eq962451
       grind)
    | exact superpose eq962451 eq2791
    | (have j0 := eq2791 x y
       grind)
    | (have r₁ := eq2791 x y
       have r₂ := eq962451
       grind)
    | exact resolve eq2791 eq962451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962451
  have eq962871 : (M.op x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq962614
  have eq962873 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq962612
  have eq962892 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq2641 x y
       grind)
    | (have r₁ := eq962873
       have r₂ := eq2641 x y
       grind)
    | exact resolve eq962873 eq2641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2641 eq962873
  have eq962902 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq962892
       grind)
    | exact superpose eq962892 eq16
    | exact resolve eq16 eq962892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962892
  have eq963127 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq962902
       have i₂ := eq962871
       grind)
    | exact superpose eq962871 eq962902
    | exact resolve eq962902 eq962871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962871
  have eq963160 : (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq963127
  have eq963216 : (k x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq963160
       grind)
    | exact superpose eq963160 eq10
    | exact resolve eq10 eq963160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963160
  have eq963659 : (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq963216
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq963216
    | exact resolve eq963216 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963216
  have eq963700 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2791 x y
       have i₂ := eq963659
       grind)
    | exact superpose eq963659 eq2791
    | (have j0 := eq2791 x y
       grind)
    | (have r₁ := eq2791 x y
       have r₂ := eq963659
       grind)
    | exact resolve eq2791 eq963659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2791 eq963659
  have eq963957 : (M.op x y) = (M.op x x) := by grind
  clear eq963700
  have eq964016 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq962902
       have i₂ := eq963957
       grind)
    | exact superpose eq963957 eq962902
    | exact resolve eq962902 eq963957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962902 eq963957
  have eq964049 : False := by grind
  exact eq964049

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_pxy_pyy_pxy_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
    | (have r₁ := eq22 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
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
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq33 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq33 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq35 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq35 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq35 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       have j1 := eq47 X0 X1
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq47 X0 X1
       grind)
    | exact resolve eq48 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq48
  have eq92 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq96 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq92 X0 X1
       have j1 := eq50 X0 X1
       grind)
    | (have r₁ := eq92 X0 X1
       have r₂ := eq50 X0 X1
       grind)
    | (have r₁ := eq92 X0 X0
       have r₂ := eq50 X0 X0
       grind)
    | exact resolve eq92 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq92
  have eq199 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq96 (σ X0) (σ X1)
       grind)
    | exact superpose eq96 eq15
    | exact resolve eq15 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 X1
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq199
    | exact resolve eq199 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq199
  have eq208 : False := by grind
  exact eq208

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_x_pxy_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq270 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
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
  have eq274 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq270 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq275 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq274 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq379 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq275 X1 X0
       grind)
    | exact superpose eq275 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq275 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq275 X0 X1
       grind)
    | exact resolve eq13 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
  have eq386 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq379 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq387 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq382
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq382
    | exact resolve eq382 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq388 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq386 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq386 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq386 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq402 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq388 X0 (τ X1)
       grind)
    | exact superpose eq388 eq18
    | (have j1 := eq388 X0 (τ X1)
       grind)
    | exact resolve eq18 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq419 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq388 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1053 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq402 (τ X0) X1
       grind)
    | exact superpose eq402 eq17
    | (have j1 := eq402 (τ X0) X1
       grind)
    | exact resolve eq17 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq402
  have eq1058 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1053 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1053
    | (have j0 := eq1053 X0 X1
       grind)
    | exact resolve eq1053 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053
  have eq1074 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1058 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1058
    | (have j0 := eq1058 X0 X1
       grind)
    | exact resolve eq1058 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq1077 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1074 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1074
    | (have j0 := eq1074 X0 X1
       grind)
    | exact resolve eq1074 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074
  have eq1141 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1077 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1077
    | (have j0 := eq1077 X1 (σ X0)
       grind)
    | exact resolve eq1077 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1392 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1141 X0 X0
       have i₂ := eq388 X0 (σ X0)
       grind)
    | exact superpose eq388 eq1141
    | (have j0 := eq1141 X1 X0
       have j1 := eq388 X0 (σ X1)
       grind)
    | exact resolve eq1141 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388 eq1141
  have eq1430 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1392 X0 X1
       have j1 := eq419 X0 (σ X1)
       grind)
    | (have r₁ := eq1392 X0 X1
       have r₂ := eq419 X0 (σ X1)
       grind)
    | exact resolve eq1392 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq1392
  have eq1720 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq1430 (σ X0) X1
       grind)
    | exact superpose eq1430 eq28
    | (have j1 := eq1430 (σ X0) X1
       grind)
    | exact resolve eq28 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1430
  have eq1731 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1720 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1720
    | (have j0 := eq1720 X0 X1
       grind)
    | exact resolve eq1720 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1720
  have eq1747 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1731 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1731
    | (have j0 := eq1731 X0 X1
       grind)
    | exact resolve eq1731 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1731
  have eq1756 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1747 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1747
    | (have j0 := eq1747 X0 X1
       grind)
    | exact resolve eq1747 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747
  have eq1847 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1756 x y
       grind)
    | exact superpose eq1756 eq16
    | (have j1 := eq1756 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1756 x y
       grind)
    | exact resolve eq16 eq1756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1756
  have eq1873 : x = (k x y) := by grind
  clear eq1847
  have eq2067 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq387
       have i₂ := eq275 y x
       grind)
    | exact superpose eq275 eq387
    | (have j1 := eq275 y x
       grind)
    | exact resolve eq387 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2070 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq2067
  have eq2071 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq2070
       have i₂ := eq1873
       grind)
    | exact superpose eq1873 eq2070
    | exact resolve eq2070 eq1873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070
  have eq2072 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2071
       have i₂ := eq1873
       grind)
    | exact superpose eq1873 eq2071
    | exact resolve eq2071 eq1873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2071
  have eq2073 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq387
       have i₂ := eq2072
       grind)
    | exact superpose eq2072 eq387
    | exact resolve eq387 eq2072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387 eq2072
  have eq2082 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2073
  have eq2083 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2082
       have i₂ := eq1873
       grind)
    | exact superpose eq1873 eq2082
    | exact resolve eq2082 eq1873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2082
  have eq2084 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2083
  have eq2086 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2084
       grind)
    | exact superpose eq2084 eq16
    | exact resolve eq16 eq2084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084
  have eq2107 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq2086
       have i₂ := eq275 y x
       grind)
    | exact superpose eq275 eq2086
    | (have j1 := eq275 y x
       grind)
    | exact resolve eq2086 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq2110 : (M.op x y) = (k x y) := by grind
  clear eq2107
  have eq2112 : x = (M.op x y) := by
    first
    | (have i₁ := eq2110
       have i₂ := eq1873
       grind)
    | exact superpose eq1873 eq2110
    | exact resolve eq2110 eq1873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1873 eq2110
  have eq2113 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2086
       have i₂ := eq2112
       grind)
    | exact superpose eq2112 eq2086
    | exact resolve eq2086 eq2112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2086 eq2112
  have eq2124 : False := by grind
  exact eq2124

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyx_pxx_pyx_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X0 X0) X1))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  clear eq23
  have eq71 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq74 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq145 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq148 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
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
  have eq2527 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq145 x y
       grind)
    | exact superpose eq145 eq16
    | (have j1 := eq145 x y
       grind)
    | exact resolve eq16 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2534 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq145 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq4574 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq74
  have eq4609 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4574 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4574
  have eq4628 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq71 X0 X0
       have i₂ := eq4609 X0
       grind)
    | exact superpose eq4609 eq71
    | (have j0 := eq71 X0 x
       have j1 := eq4609 X0
       grind)
    | exact resolve eq71 eq4609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq4609
  have eq4679 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4628 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4628
  have eq4697 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4679 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq4679 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq4679 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4679
  have eq4757 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4697 (σ X0)
       grind)
    | exact superpose eq4697 eq15
    | exact resolve eq15 eq4697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4776 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4757 X0
       have i₂ := eq4697 X0
       grind)
    | exact superpose eq4697 eq4757
    | exact resolve eq4757 eq4697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4697 eq4757
  have eq8642 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq148
    | exact resolve eq148 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq8726 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8642 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8642
    | (have j0 := eq8642 X0 X1
       grind)
    | exact resolve eq8642 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8642
  have eq15646 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2534 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq2534
    | (have j0 := eq2534 (τ X0) (τ X1)
       grind)
    | exact resolve eq2534 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq15707 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15646 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq15646
    | (have j0 := eq15646 X0 X1
       grind)
    | exact resolve eq15646 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15646
  have eq15742 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15707 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq15707
    | (have j0 := eq15707 X0 X1
       grind)
    | exact resolve eq15707 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15707
  have eq15773 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15742 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq15742
    | (have j0 := eq15742 X0 X1
       grind)
    | exact resolve eq15742 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15742
  have eq15780 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15773 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15773
    | (have j0 := eq15773 X0 X1
       grind)
    | exact resolve eq15773 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15773
  have eq15784 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ X0 = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15780 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15780
    | (have j0 := eq15780 X0 X1
       grind)
    | exact resolve eq15780 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15780
  have eq15786 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15784 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15784
    | (have j0 := eq15784 X0 X1
       grind)
    | exact resolve eq15784 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15784
  have eq45688 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2527
       have i₂ := eq8726 y x
       grind)
    | exact superpose eq8726 eq2527
    | (have j1 := eq8726 (σ x) (σ y)
       grind)
    | (have r₁ := eq2527
       have r₂ := eq8726 y x
       grind)
    | (have r₁ := eq2527
       have r₂ := eq8726 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2527
       have r₂ := eq8726 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2527 eq8726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2527 eq8726
  have eq45689 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq45688
  have eq58100 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq45689
       grind)
    | exact superpose eq45689 eq16
    | exact resolve eq16 eq45689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45689
  have eq58101 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq58100
       have r₂ := eq4776 x
       grind)
    | exact resolve eq58100 eq4776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58100
  have eq58102 : x ≠ x ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq58101
       grind)
    | exact superpose eq58101 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq58101
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq58101
       grind)
    | exact resolve eq12 eq58101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58101
  have eq58109 : x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq58102
  have eq58113 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2534 x y
       have i₂ := eq58109
       grind)
    | exact superpose eq58109 eq2534
    | (have j0 := eq2534 x y
       grind)
    | exact resolve eq2534 eq58109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2534 eq58109
  have eq58125 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq58113
  have eq58126 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq58125
  have eq58132 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58126
       grind)
    | exact superpose eq58126 eq16
    | exact resolve eq16 eq58126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58134 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq58126
       grind)
    | exact superpose eq58126 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq58126
       grind)
    | exact resolve eq12 eq58126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58126
  have eq58141 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq58134
  have eq58143 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq58141
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq58141
    | exact resolve eq58141 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58141
  have eq58152 : y = (τ (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq58143
       grind)
    | exact superpose eq58143 eq10
    | exact resolve eq10 eq58143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58143
  have eq58261 : x = y ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq58152
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq58152
    | exact resolve eq58152 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58152
  have eq58295 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58261
       grind)
    | exact superpose eq58261 eq16
    | exact resolve eq16 eq58261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58261
  have eq58296 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq58295
       have r₂ := eq4776 x
       grind)
    | exact resolve eq58295 eq4776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58295
  have eq58304 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq58296
       grind)
    | exact superpose eq58296 eq10
    | exact resolve eq10 eq58296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58296
  have eq58414 : x = (k y x) := by
    first
    | (have i₁ := eq58304
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq58304
    | exact resolve eq58304 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58304
  have eq58454 : x ≠ x ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15786 y x
       have i₂ := eq58414
       grind)
    | exact superpose eq58414 eq15786
    | (have j0 := eq15786 x y
       grind)
    | (have r₁ := eq15786 y x
       have r₂ := eq58414
       grind)
    | exact resolve eq15786 eq58414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15786 eq58414
  have eq58459 : x = y ∨ x = (M.op x y) := by grind
  clear eq58454
  have eq58463 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58459
       grind)
    | exact superpose eq58459 eq16
    | exact resolve eq16 eq58459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58459
  have eq58468 : x = (M.op x y) := by
    first
    | (have r₁ := eq58463
       have r₂ := eq4776 x
       grind)
    | exact resolve eq58463 eq4776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58463
  have eq58472 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq58132
       have i₂ := eq58468
       grind)
    | exact superpose eq58468 eq58132
    | exact resolve eq58132 eq58468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58132 eq58468
  have eq58481 : (σ x) = (σ y) := by grind
  clear eq58472
  have eq58483 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq58481
       grind)
    | exact superpose eq58481 eq10
    | exact resolve eq10 eq58481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58481
  have eq58592 : x = y := by
    first
    | (have i₁ := eq58483
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq58483
    | exact resolve eq58483 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58483
  have eq58623 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58592
       grind)
    | exact superpose eq58592 eq16
    | exact resolve eq16 eq58592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58592
  have eq58629 : False := by grind
  exact eq58629

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pxy_pxx_pxy_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq198 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq83 X1 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq200 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq198 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq201 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq200 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq203 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq201 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq201
    | (have j0 := eq201 X0 X1
       grind)
    | exact resolve eq201 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq207 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq203 X0 X1
       have j1 := eq199 X0 X1
       grind)
    | (have r₁ := eq203 X0 X1
       have r₂ := eq199 X0 X1
       grind)
    | (have r₁ := eq203 (k X0 X1) X0
       have r₂ := eq199 X0 X1
       grind)
    | (have r₁ := eq203 X0 X0
       have r₂ := eq199 X0 X0
       grind)
    | exact resolve eq203 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq203
  have eq517 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq207 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq207
    | exact resolve eq207 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq525 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq207 x y
       grind)
    | exact superpose eq207 eq16
    | (have j1 := eq207 x y
       grind)
    | exact resolve eq16 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq538 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq517 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq517
    | (have j0 := eq517 X0 X1
       grind)
    | exact resolve eq517 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq517
  have eq540 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq538 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq538
    | exact resolve eq538 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq599 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq540 (τ X0) X1
       grind)
    | exact superpose eq540 eq18
    | (have j1 := eq540 (τ X0) X1
       grind)
    | exact resolve eq18 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq540
  have eq825 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq599 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq599
    | exact resolve eq599 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq880 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq825 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq825
    | (have j0 := eq825 X0 X1
       grind)
    | exact resolve eq825 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq977 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq525
       have i₂ := eq880 x y
       grind)
    | exact superpose eq880 eq525
    | (have j1 := eq880 (σ x) (σ y)
       grind)
    | (have r₁ := eq525
       have r₂ := eq880 x y
       grind)
    | exact resolve eq525 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq978 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq977
  have eq984 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq978
  have eq1017 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq525
       have i₂ := eq984
       grind)
    | exact superpose eq984 eq525
    | exact resolve eq525 eq984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525 eq984
  have eq1018 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1017
  have eq1019 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1018
  have eq1032 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1019
  have eq1037 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1032
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1032
    | exact resolve eq1032 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq1061 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1037
       grind)
    | exact superpose eq1037 eq16
    | exact resolve eq16 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037
  have eq1067 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1061
       have i₂ := eq880 x y
       grind)
    | exact superpose eq880 eq1061
    | (have j1 := eq880 x y
       grind)
    | (have r₁ := eq1061
       have r₂ := eq880 x y
       grind)
    | exact resolve eq1061 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq1068 : x = (M.op y y) := by grind
  clear eq1067
  have eq1107 : (M.op x y) = (k x y) := by grind
  clear eq1068
  have eq1111 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1061
       have i₂ := eq1107
       grind)
    | exact superpose eq1107 eq1061
    | exact resolve eq1061 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061 eq1107
  have eq1114 : False := by grind
  exact eq1114

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pyx_pxy_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq28 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
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
  clear eq19
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
  have eq317 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq317
  have eq323 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq318 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq336 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq323 (σ X0)
       grind)
    | exact superpose eq323 eq15
    | exact resolve eq15 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq323 (τ X0)
       grind)
    | exact superpose eq323 eq32
    | exact resolve eq32 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq342 X0
       have i₂ := eq323 X0
       grind)
    | exact superpose eq323 eq342
    | exact resolve eq342 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq355 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq336 X0
       have i₂ := eq323 X0
       grind)
    | exact superpose eq323 eq336
    | exact resolve eq336 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq693 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq704 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (M.op (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X0 X1 X2
       have i₂ := eq14 (k (σ X0) X1) (σ X2)
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 (k (σ X0) X1) (σ X2)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq704 X0 X1 X2
       have i₂ := eq355 X2
       grind)
    | exact superpose eq355 eq704
    | (have j0 := eq704 X0 X1 X2
       grind)
    | exact resolve eq704 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq710 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq693 X0 X1
       have i₂ := eq355 X1
       grind)
    | exact superpose eq355 eq693
    | (have j0 := eq693 X0 X1
       grind)
    | exact resolve eq693 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq3726 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq710 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq710
    | exact resolve eq710 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq3798 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3726 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq3726
    | (have j0 := eq3726 X0 X1
       grind)
    | exact resolve eq3726 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3726
  have eq6281 : ∀ X0 X1 : G, (M.op (τ X0) (σ X1)) = (M.op (σ X1) (τ X0)) ∨ (τ X0) = (σ (M.op X1 X1)) ∨ (k X0 (σ (σ X1))) = (σ (M.op (τ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (σ X1)
       have i₂ := eq3798 (τ X0) X1
       grind)
    | exact superpose eq3798 eq18
    | (have j1 := eq3798 (τ X0) X1
       grind)
    | exact resolve eq18 eq3798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3798
  have eq98954 : ∀ X0 X1 : G, (M.op (τ X0) (σ X1)) ≠ (M.op (τ X0) (σ X1)) ∨ (τ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (τ X0) (σ X1)) = (k (τ X0) (σ X1)) ∨ (τ X0) = (σ (M.op X1 X1)) ∨ (k X0 (σ (σ X1))) = (σ (M.op (τ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) (σ X1)
       have i₂ := eq6281 X0 X1
       grind)
    | exact superpose eq6281 eq13
    | (have j0 := eq13 (τ X0) (σ X1)
       have j1 := eq6281 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (σ X1)
       have r₂ := eq6281 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (τ X0)
       have r₂ := eq6281 X0 X1
       grind)
    | exact resolve eq13 eq6281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6281
  have eq98956 : ∀ X0 X1 : G, (τ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (τ X0) (σ X1)) = (k (τ X0) (σ X1)) ∨ (τ X0) = (σ (M.op X1 X1)) ∨ (k X0 (σ (σ X1))) = (σ (M.op (τ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq98954 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98954
  have eq98960 : ∀ X0 X1 : G, (τ X0) = (σ (M.op X1 X1)) ∨ (M.op (τ X0) (σ X1)) = (k (τ X0) (σ X1)) ∨ (τ X0) = (σ (M.op X1 X1)) ∨ (k X0 (σ (σ X1))) = (σ (M.op (τ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq98956 X0 X1
       have i₂ := eq355 X1
       grind)
    | exact superpose eq355 eq98956
    | (have j0 := eq98956 X0 X1
       grind)
    | exact resolve eq98956 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98956
  have eq98961 : ∀ X0 X1 : G, (k X0 (σ (σ X1))) = (σ (M.op (τ X0) (σ X1))) ∨ (M.op (τ X0) (σ X1)) = (k (τ X0) (σ X1)) ∨ (τ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq98960 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98960
  have eq364665 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (σ X2)) ≠ (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k (σ X0) X1) (σ X2)
       have i₂ := eq707 X0 X1 X2
       grind)
    | exact superpose eq707 eq13
    | (have j0 := eq13 (k (σ X0) X1) (σ X2)
       have j1 := eq707 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq707 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k (σ X0) X1)
       have r₂ := eq707 X0 X1 X2
       grind)
    | exact resolve eq13 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq364667 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq364665 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364665
  have eq364671 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (M.op X2 X2)) ∨ (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq364667 X0 X1 X2
       have i₂ := eq355 X2
       grind)
    | exact superpose eq355 eq364667
    | (have j0 := eq364667 X0 X1 X2
       grind)
    | exact resolve eq364667 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364667
  have eq364672 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (M.op X2 X2)) ∨ (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq364671 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364671
  have eq365021 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (M.op X2 X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq364672 X0 X1 X2
       have i₂ := eq28 X0 X1 X2
       grind)
    | exact superpose eq28 eq364672
    | (have j0 := eq364672 X0 X1 X2
       grind)
    | exact resolve eq364672 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq364672
  have eq365022 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq365021 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365021
  have eq365401 : ∀ X0 X1 X2 : G, (σ (k (τ (k X0 X1)) X2)) = (M.op (k (σ (τ X0)) X1) (σ X2)) ∨ (k (σ (τ X0)) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq365022 (τ X0) X1 X2
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq365022
    | (have j0 := eq365022 (τ X0) X1 X2
       grind)
    | exact resolve eq365022 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq365022
  have eq366223 : ∀ X0 X1 X2 : G, (σ (k (τ (k X0 X1)) X2)) = (M.op (k X0 X1) (σ X2)) ∨ (k (σ (τ X0)) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq365401 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq365401
    | (have j0 := eq365401 X0 X1 X2
       grind)
    | exact resolve eq365401 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365401
  have eq366525 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (M.op (k X0 X1) (σ X2)) ∨ (k (σ (τ X0)) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq366223 X0 X1 X2
       have i₂ := eq18 (k X0 X1) X2
       grind)
    | exact superpose eq18 eq366223
    | (have j0 := eq366223 X0 X1 X2
       grind)
    | exact resolve eq366223 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366223
  have eq366756 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (M.op (k X0 X1) (σ X2)) ∨ (k X0 X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq366525 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq366525
    | (have j0 := eq366525 X0 X1 X2
       grind)
    | exact resolve eq366525 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366525
  have eq367469 : ∀ X0 X1 X2 : G, (k (k X1 X2) X0) = (M.op (k X1 X2) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq366756 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq366756
    | (have j0 := eq366756 X1 X2 (τ X0)
       grind)
    | exact resolve eq366756 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366756
  have eq368039 : ∀ X0 X1 X2 : G, (k X1 X2) = (σ (τ (M.op X0 X0))) ∨ (k (k X1 X2) X0) = (M.op (k X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq367469 X0 X1 X2
       have i₂ := eq349 X0
       grind)
    | exact superpose eq349 eq367469
    | (have j0 := eq367469 X0 X1 X2
       grind)
    | exact resolve eq367469 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367469
  have eq368089 : ∀ X0 X1 X2 : G, (k (k X1 X2) X0) = (M.op (k X1 X2) X0) ∨ (M.op X0 X0) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq368039 X0 X1 X2
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq368039
    | (have j0 := eq368039 X0 X1 X2
       grind)
    | exact resolve eq368039 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368039
  have eq368178 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq368089 X0 X0 X0
       have i₂ := eq323 X0
       grind)
    | exact superpose eq323 eq368089
    | exact resolve eq368089 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq368089
  have eq370064 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    grind
  clear eq368178
  have eq370194 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq370064 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370064
  have eq370205 : ∀ X0 X1 : G, (k (σ (M.op X0 X0)) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq370194 (σ X0) X1
       have i₂ := eq355 X0
       grind)
    | exact superpose eq355 eq370194
    | exact resolve eq370194 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq370823 : ∀ X0 X1 : G, (σ (k (M.op X0 X0) X1)) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op X0 X0) X1
       have i₂ := eq370205 X0 (σ X1)
       grind)
    | exact superpose eq370205 eq15
    | exact resolve eq15 eq370205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370205
  have eq371321 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X1)) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq370823 X0 X1
       have i₂ := eq370194 X0 X1
       grind)
    | exact superpose eq370194 eq370823
    | exact resolve eq370823 eq370194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370823
  have eq4485022 : ∀ X0 X1 : G, (M.op (τ X0) (σ X1)) = (τ (k X0 (σ (σ X1)))) ∨ (M.op (τ X0) (σ X1)) = (k (τ X0) (σ X1)) ∨ (τ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) (σ X1))
       have i₂ := eq98961 X0 X1
       grind)
    | exact superpose eq98961 eq10
    | (have j1 := eq98961 X0 X1
       grind)
    | exact resolve eq10 eq98961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98961
  have eq4485972 : ∀ X0 X1 : G, (M.op (τ X0) (σ X1)) = (k (τ X0) (σ X1)) ∨ (M.op (τ X0) (σ X1)) = (k (τ X0) (σ X1)) ∨ (τ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4485022 X0 X1
       have i₂ := eq23 X0 (σ X1)
       grind)
    | exact superpose eq23 eq4485022
    | (have j0 := eq4485022 X0 X1
       grind)
    | exact resolve eq4485022 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq4485022
  have eq4485973 : ∀ X0 X1 : G, (M.op (τ X0) (σ X1)) = (k (τ X0) (σ X1)) ∨ (τ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4485972 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4485972
  have eq4487941 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4485973 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4485973
    | exact resolve eq4485973 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4485973
  have eq4491239 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4487941 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4487941
    | (have j0 := eq4487941 X1 (τ X0)
       grind)
    | exact resolve eq4487941 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4492058 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq4487941 (σ X0) X1
       grind)
    | exact superpose eq4487941 eq15
    | (have j1 := eq4487941 (σ X0) X1
       grind)
    | exact resolve eq15 eq4487941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4487941
  have eq4493182 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4491239 X0 X1
       have i₂ := eq349 X0
       grind)
    | exact superpose eq349 eq4491239
    | (have j0 := eq4491239 X0 X1
       grind)
    | exact resolve eq4491239 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349 eq4491239
  have eq4493722 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4493182 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4493182
    | (have j0 := eq4493182 X0 X1
       grind)
    | exact resolve eq4493182 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4493182
  have eq4496268 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq4493722 X1 (τ X0)
       grind)
    | exact superpose eq4493722 eq18
    | (have j1 := eq4493722 X1 (τ X0)
       grind)
    | exact resolve eq18 eq4493722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4493722
  have eq4529442 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4496268 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4496268
    | exact resolve eq4496268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4496268
  have eq4531090 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4529442 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4529442
    | (have j0 := eq4529442 X0 X1
       grind)
    | exact resolve eq4529442 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4529442
  have eq4548939 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4492058 x y
       grind)
    | exact superpose eq4492058 eq16
    | (have j1 := eq4492058 x y
       grind)
    | exact resolve eq16 eq4492058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4492058
  have eq4553737 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq4548939
       have i₂ := eq4531090 x y
       grind)
    | exact superpose eq4531090 eq4548939
    | (have j1 := eq4531090 x y
       grind)
    | (have r₁ := eq4548939
       have r₂ := eq4531090 x y
       grind)
    | exact resolve eq4548939 eq4531090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4531090
  have eq4553741 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq4553737
  have eq4553812 : ∀ X0 : G, (σ x) = (σ (M.op y y)) ∨ (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq370194 y x
       have i₂ := eq4553741
       grind)
    | exact superpose eq4553741 eq370194
    | exact resolve eq370194 eq4553741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4553741
  have eq4554527 : ∀ X0 : G, (M.op y y) = (τ (σ x)) ∨ (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq4553812 X0
       grind)
    | exact superpose eq4553812 eq10
    | (have j1 := eq4553812 X0
       grind)
    | exact resolve eq10 eq4553812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4553812
  have eq4555572 : ∀ X0 : G, x = (M.op y y) ∨ (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq4554527 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4554527
    | (have j0 := eq4554527 X0
       grind)
    | exact resolve eq4554527 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4554527
  have eq4556336 : ∀ X0 X1 : G, (M.op x X0) = (k x X0) ∨ (M.op x X1) = (k x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq370194 y X1
       have i₂ := eq4555572 X0
       grind)
    | exact superpose eq4555572 eq370194
    | (have j1 := eq4555572 X0
       grind)
    | exact resolve eq370194 eq4555572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370194 eq4555572
  have eq4557923 : ∀ X0 : G, (M.op x X0) ≠ (M.op x X0) ∨ (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have j0 := eq4556336 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4556336
  have eq4557924 : ∀ X0 : G, (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have j0 := eq4557923 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4557923
  have eq4557950 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4548939
       have i₂ := eq4557924 y
       grind)
    | exact superpose eq4557924 eq4548939
    | exact resolve eq4548939 eq4557924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4548939 eq4557924
  have eq4558937 : (σ x) = (σ (M.op y y)) := by grind
  clear eq4557950
  have eq4560510 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq4558937
       grind)
    | exact superpose eq4558937 eq10
    | exact resolve eq10 eq4558937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4558937
  have eq4561555 : x = (M.op y y) := by
    first
    | (have i₁ := eq4560510
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4560510
    | exact resolve eq4560510 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4560510
  have eq4562626 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq371321 y x
       have i₂ := eq4561555
       grind)
    | exact superpose eq4561555 eq371321
    | exact resolve eq371321 eq4561555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371321 eq4561555
  have eq4586446 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4562626 y
       grind)
    | exact superpose eq4562626 eq16
    | (have r₁ := eq16
       have r₂ := eq4562626 y
       grind)
    | exact resolve eq16 eq4562626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4562626
  have eq4587068 : False := by grind
  exact eq4587068

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
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
  have eq82 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq190 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq82 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq82 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq82 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq199 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq190 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq200 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq199 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq202 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq200 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq200
    | (have j0 := eq200 X0 X1
       grind)
    | exact resolve eq200 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq205 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq202 X0 X1
       have j1 := eq196 X1 X0
       grind)
    | (have r₁ := eq202 X1 X0
       have r₂ := eq196 X0 X1
       grind)
    | (have r₁ := eq202 X1 (k X0 X1)
       have r₂ := eq196 X0 X1
       grind)
    | (have r₁ := eq202 X1 X1
       have r₂ := eq196 X1 X1
       grind)
    | exact resolve eq202 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq202
  have eq537 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq205 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq205
    | exact resolve eq205 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq545 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq205 y x
       grind)
    | exact superpose eq205 eq16
    | (have j1 := eq205 y x
       grind)
    | exact resolve eq16 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq557 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq537 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq537
    | (have j0 := eq537 X0 X1
       grind)
    | exact resolve eq537 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq537
  have eq559 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq557 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq557
    | exact resolve eq557 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq620 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq559 (τ X0) X1
       grind)
    | exact superpose eq559 eq18
    | (have j1 := eq559 (τ X0) X1
       grind)
    | exact resolve eq18 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq559
  have eq788 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq620 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq620
    | exact resolve eq620 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq839 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq788 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq788
    | (have j0 := eq788 X0 X1
       grind)
    | exact resolve eq788 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq954 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq545
       have i₂ := eq839 x y
       grind)
    | exact superpose eq839 eq545
    | (have j1 := eq839 (σ x) (σ y)
       grind)
    | (have r₁ := eq545
       have r₂ := eq839 x y
       grind)
    | exact resolve eq545 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq955 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq954
  have eq1001 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq955
  have eq1005 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq545
       have i₂ := eq1001
       grind)
    | exact superpose eq1001 eq545
    | exact resolve eq545 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545 eq1001
  have eq1006 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1005
  have eq1007 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1006
  have eq1048 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1007
  have eq1053 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1048
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1048
    | exact resolve eq1048 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq1058 : (σ (M.op x y)) ≠ (σ (k x y)) := by
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
  have eq1081 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1058
       have i₂ := eq839 x y
       grind)
    | exact superpose eq839 eq1058
    | (have j1 := eq839 x y
       grind)
    | (have r₁ := eq1058
       have r₂ := eq839 x y
       grind)
    | exact resolve eq1058 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq1082 : x = (M.op y y) := by grind
  clear eq1081
  have eq1089 : (M.op x y) = (k x y) := by grind
  clear eq1082
  have eq1125 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1058
       have i₂ := eq1089
       grind)
    | exact superpose eq1089 eq1058
    | exact resolve eq1058 eq1089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058 eq1089
  have eq1128 : False := by grind
  exact eq1128

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
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
  have eq27 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq39 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq41 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq27 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq99 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq275 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq276 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq275 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq281 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq276 X0 X1
       have j1 := eq99 X0 X1
       grind)
    | (have r₁ := eq276 X0 X1
       have r₂ := eq99 X0 X1
       grind)
    | (have r₁ := eq276 X0 X0
       have r₂ := eq99 X0 X0
       grind)
    | exact resolve eq276 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq276
  have eq292 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq281 (σ X1) (σ X0)
       grind)
    | exact superpose eq281 eq15
    | exact resolve eq15 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq292 X0 X1
       have i₂ := eq281 X1 X0
       grind)
    | exact superpose eq281 eq292
    | exact resolve eq292 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq292
  have eq299 : False := by grind
  exact eq299
