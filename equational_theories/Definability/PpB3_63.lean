import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_pxx_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq263 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq264 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq263 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq263
    | (have j0 := eq263 (σ X0) (σ X1)
       grind)
    | exact resolve eq263 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq263 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq263
    | (have j0 := eq263 (τ X0) (τ X1)
       grind)
    | exact resolve eq263 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq400 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq264 X1 X0
       have i₂ := eq263 X1 X0
       grind)
    | exact superpose eq263 eq264
    | (have j0 := eq264 X1 X0
       have j1 := eq263 (σ X1) (σ X0)
       grind)
    | exact resolve eq264 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq540 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq265 X0 X0
       grind)
    | exact superpose eq265 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq265 X0 X0
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq265 X0 X0
       grind)
    | exact resolve eq12 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq544 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X1 X0)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq265 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq546 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq540 X0 X1
       have j1 := eq12 X1 (τ X0)
       grind)
    | (have r₁ := eq540 X0 X1
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq540 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq553 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq544 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq544
    | (have j0 := eq544 (σ X1) (σ X0)
       grind)
    | exact resolve eq544 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq563 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 X1) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq553 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq553
    | (have j0 := eq553 X0 X1
       grind)
    | exact resolve eq553 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq565 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq563 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq563
    | (have j0 := eq563 X0 X1
       grind)
    | exact resolve eq563 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq566 : ∀ X0 X1 : G, (M.op (τ (σ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq565 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq565
    | (have j0 := eq565 X0 X1
       grind)
    | exact resolve eq565 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq567 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq566 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq566
    | (have j0 := eq566 X0 X1
       grind)
    | exact resolve eq566 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq569 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq567 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq567
    | (have j0 := eq567 (σ X0) (σ X1)
       grind)
    | exact resolve eq567 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq624 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq546 (σ X0) X1
       have i₂ := eq28 X0 (σ X0)
       grind)
    | exact superpose eq28 eq546
    | (have j0 := eq546 (σ X0) X1
       grind)
    | exact resolve eq546 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq625 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq624 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq624
    | (have j0 := eq624 X0 X1
       grind)
    | exact resolve eq624 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq628 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq625 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq625
    | (have j0 := eq625 X0 X1
       grind)
    | exact resolve eq625 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq633 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq628 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq628
    | (have j0 := eq628 (σ X0) X1
       grind)
    | exact resolve eq628 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq4871 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq400 x y
       grind)
    | exact superpose eq400 eq16
    | (have j1 := eq400 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq400 x y
       grind)
    | exact resolve eq16 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq4885 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4871
  have eq4905 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4885
       grind)
    | exact superpose eq4885 eq16
    | exact resolve eq16 eq4885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4908 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq4885
       grind)
    | exact superpose eq4885 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq4885
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq4885
       grind)
    | exact resolve eq13 eq4885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4909 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9 (σ y) (σ x)
       have i₂ := eq4885
       grind)
    | exact superpose eq4885 eq9
    | exact resolve eq9 eq4885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4885
  have eq4910 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq4908
  have eq4912 : (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4910
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4910
    | exact resolve eq4910 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4910
  have eq4914 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq263 eq4912
    | (have j1 := eq263 (σ x) (σ x)
       grind)
    | exact resolve eq4912 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq4912
  have eq4919 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9 (σ y) (σ y)
       have i₂ := eq4909
       grind)
    | exact superpose eq4909 eq9
    | exact resolve eq9 eq4909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4909
  have eq19218 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4919 eq4914
    | exact resolve eq4914 eq4919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4914 eq4919
  have eq19219 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq19218
       have r₂ := eq4905
       grind)
    | exact resolve eq19218 eq4905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4905 eq19218
  have eq19221 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq19219
       grind)
    | exact superpose eq19219 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq19219
       grind)
    | exact resolve eq12 eq19219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19226 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq19221 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19221
  have eq19246 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq19226 (σ X0)
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq19226
    | exact resolve eq19226 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19278 : ∀ X0 : G, (τ (σ x)) ≠ (τ (M.op (σ x) (σ x))) ∨ (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq546 (σ x) X0
       have i₂ := eq19226 (σ x)
       grind)
    | exact superpose eq19226 eq546
    | (have j0 := eq546 (σ x) X0
       grind)
    | exact resolve eq546 eq19226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq19226
  have eq19386 : ∀ X0 : G, x ≠ (τ (M.op (σ x) (σ x))) ∨ (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq19278 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19278
    | (have j0 := eq19278 X0
       grind)
    | exact resolve eq19278 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19278
  have eq19397 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x ≠ (τ (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq19386 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19386
    | exact resolve eq19386 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19386
  have eq19399 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x ≠ (τ (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19219 eq19397
    | (have j0 := eq19397 X0
       grind)
    | exact resolve eq19397 eq19219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19219 eq19397
  have eq19401 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq19399 X0
       grind)
    | (have r₁ := eq19399 X0
       have r₂ := eq10 x
       grind)
    | exact resolve eq19399 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19399
  have eq19646 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19401 eq19246
    | exact resolve eq19246 eq19401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19246 eq19401
  have eq19691 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19646 y
       grind)
    | exact superpose eq19646 eq16
    | (have r₁ := eq16
       have r₂ := eq19646 y
       grind)
    | exact resolve eq16 eq19646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19646
  have eq19718 : y = (M.op x y) := by grind
  clear eq19691
  have eq19814 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19718
       grind)
    | exact superpose eq19718 eq16
    | exact resolve eq16 eq19718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19815 : y = (M.op y (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq19718
       grind)
    | exact superpose eq19718 eq9
    | exact resolve eq9 eq19718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19816 : y ≠ y ∨ x = (M.op x x) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19718
       grind)
    | exact superpose eq19718 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19718
       grind)
    | exact resolve eq13 eq19718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19821 : x = (M.op x x) ∨ (k y x) = (M.op y y) := by grind
  clear eq19816
  have eq19827 : y = (M.op y y) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq19815
       grind)
    | exact superpose eq19815 eq9
    | exact resolve eq9 eq19815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19815
  have eq20922 : y = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq19821
       have i₂ := eq19827
       grind)
    | exact superpose eq19827 eq19821
    | exact resolve eq19821 eq19827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19821 eq19827
  have eq20929 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq569 y x
       have i₂ := eq20922
       grind)
    | exact superpose eq20922 eq569
    | (have j0 := eq569 y x
       grind)
    | exact resolve eq569 eq20922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569 eq20922
  have eq20932 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq20929
  have eq20939 : x = (M.op x x) := by
    first
    | (have r₁ := eq20932
       have r₂ := eq19814
       grind)
    | exact resolve eq20932 eq19814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20932
  have eq20941 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq20939
       grind)
    | exact superpose eq20939 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq20939
       grind)
    | exact resolve eq12 eq20939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20946 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq20941 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20941
  have eq20967 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq633 x X0
       have i₂ := eq20946 x
       grind)
    | exact superpose eq20946 eq633
    | (have j0 := eq633 x X0
       grind)
    | exact resolve eq633 eq20946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq21011 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq20967 X0
       have i₂ := eq20939
       grind)
    | exact superpose eq20939 eq20967
    | (have j0 := eq20967 X0
       grind)
    | exact resolve eq20967 eq20939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20939 eq20967
  have eq21012 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq21011 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21011
  have eq21148 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq21012 (σ X0)
       grind)
    | exact superpose eq21012 eq15
    | exact resolve eq15 eq21012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21012
  have eq21234 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq21148 X0
       have i₂ := eq20946 X0
       grind)
    | exact superpose eq20946 eq21148
    | exact resolve eq21148 eq20946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20946 eq21148
  have eq21648 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq19814
       have i₂ := eq21234 y
       grind)
    | exact superpose eq21234 eq19814
    | exact resolve eq19814 eq21234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19814 eq21234
  have eq21696 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq21648
       have i₂ := eq19718
       grind)
    | exact superpose eq19718 eq21648
    | exact resolve eq21648 eq19718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19718 eq21648
  have eq21697 : False := by grind
  exact eq21697

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
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
    | (have r₁ := eq270 x
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
  have eq348 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq302 X0
       grind)
    | exact superpose eq302 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq302 X0
       grind)
    | exact superpose eq302 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq351 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
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
  have eq399 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
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
  have eq403 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
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
  have eq422 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq403
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq403
    | exact resolve eq403 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq430 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq399 X0 X1
       grind)
    | exact superpose eq399 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq399 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq399 X0 X1
       grind)
    | exact resolve eq13 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq430 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq442 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq440 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq440 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq440 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq470 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq442 X0 (τ X1)
       grind)
    | exact superpose eq442 eq17
    | (have j1 := eq442 X0 (τ X1)
       grind)
    | exact resolve eq17 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq476 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq442 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1593 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq470 (τ X0) X1
       grind)
    | exact superpose eq470 eq18
    | (have j1 := eq470 (τ X0) X1
       grind)
    | exact resolve eq18 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq470
  have eq1600 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1593 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1593
    | (have j0 := eq1593 X0 X1
       grind)
    | exact resolve eq1593 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593
  have eq1619 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1600 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1600
    | (have j0 := eq1600 X0 X1
       grind)
    | exact resolve eq1600 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1600
  have eq1624 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1619 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1619
    | (have j0 := eq1619 X0 X1
       grind)
    | exact resolve eq1619 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619
  have eq1689 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1624 X0 X1
       have i₂ := eq442 X0 X1
       grind)
    | exact superpose eq442 eq1624
    | (have j0 := eq1624 X0 X1
       have j1 := eq442 X0 X1
       grind)
    | exact resolve eq1624 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442 eq1624
  have eq1761 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1689 X0 X1
       have j1 := eq476 X1 X0
       grind)
    | (have r₁ := eq1689 X1 X0
       have r₂ := eq476 X0 X1
       grind)
    | exact resolve eq1689 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476 eq1689
  have eq1797 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1761 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1761
    | (have j0 := eq1761 X1 (σ X0)
       grind)
    | exact resolve eq1761 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1761
  have eq2510 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq1797 X1 (σ X0)
       grind)
    | exact superpose eq1797 eq22
    | (have j1 := eq1797 X1 (σ X0)
       grind)
    | exact resolve eq22 eq1797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1797
  have eq2520 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2510 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2510
    | (have j0 := eq2510 X0 X1
       grind)
    | exact resolve eq2510 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2510
  have eq2535 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2520 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2520
    | (have j0 := eq2520 X0 X1
       grind)
    | exact resolve eq2520 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2520
  have eq2544 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2535 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2535
    | (have j0 := eq2535 X0 X1
       grind)
    | exact resolve eq2535 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2535
  have eq2568 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2544 x y
       grind)
    | exact superpose eq2544 eq16
    | (have j1 := eq2544 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2544 x y
       grind)
    | exact resolve eq16 eq2544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2544
  have eq2606 : x = (k y x) := by grind
  clear eq2568
  have eq2908 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
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
  have eq2909 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq2908
  have eq2911 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq2909
       have i₂ := eq2606
       grind)
    | exact superpose eq2606 eq2909
    | exact resolve eq2909 eq2606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2909
  have eq2913 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2911
       have i₂ := eq2606
       grind)
    | exact superpose eq2606 eq2911
    | exact resolve eq2911 eq2606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2911
  have eq2915 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
  have eq2928 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2915
  have eq2929 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2928
       have i₂ := eq2606
       grind)
    | exact superpose eq2606 eq2928
    | exact resolve eq2928 eq2606
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
  have eq2966 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k y x) := by
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
  have eq2967 : (M.op x y) = (k y x) := by grind
  clear eq2966
  have eq2970 : x = (M.op x y) := by
    first
    | (have i₁ := eq2967
       have i₂ := eq2606
       grind)
    | exact superpose eq2606 eq2967
    | exact resolve eq2967 eq2606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2606 eq2967
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

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
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
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq64 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq74 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq65 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq75 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq74 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq90 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq75 (σ X0)
       grind)
    | exact superpose eq75 eq15
    | exact resolve eq15 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq90
    | exact resolve eq90 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq90
  have eq118 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq101
    | (have j1 := eq14 (σ X0) (σ (M.op X0 X0))
       grind)
    | exact resolve eq101 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq132 X0 X1
       have j1 := eq118 X0 X1
       grind)
    | (have r₁ := eq132 X0 X1
       have r₂ := eq118 X0 X1
       grind)
    | (have r₁ := eq132 X0 (σ (M.op X0 X0))
       have r₂ := eq118 X0 X1
       grind)
    | (have r₁ := eq132 (M.op X0 X0) (σ X0)
       have r₂ := eq118 X0 X1
       grind)
    | exact resolve eq132 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq132
  have eq163 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq141 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq141
    | exact resolve eq141 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq141 X0 (σ X1)
       grind)
    | exact superpose eq141 eq15
    | (have j1 := eq141 (k X1 X0) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq175 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq163 (τ X0) X1
       grind)
    | exact superpose eq163 eq19
    | (have j1 := eq163 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq163
  have eq261 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq175 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq175
    | exact resolve eq175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq286 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq261 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq261
    | (have j0 := eq261 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq261 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq836 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq168 x y
       grind)
    | exact superpose eq168 eq16
    | (have j1 := eq168 x y
       grind)
    | exact resolve eq16 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq848 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq836
       have i₂ := eq286 x y
       grind)
    | exact superpose eq286 eq836
    | (have j1 := eq286 (σ x) (σ y)
       grind)
    | (have r₁ := eq836
       have r₂ := eq286 x y
       grind)
    | (have r₁ := eq836
       have r₂ := eq286 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq836
       have r₂ := eq286 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq836 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286 eq836
  have eq849 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq848
  have eq851 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq849
       grind)
    | exact superpose eq849 eq16
    | exact resolve eq16 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq852 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq851
       have r₂ := eq101 x
       grind)
    | exact resolve eq851 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq853 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq852
       grind)
    | exact superpose eq852 eq16
    | exact resolve eq16 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq854 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq852
       grind)
    | exact superpose eq852 eq10
    | exact resolve eq10 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq895 : x = y := by
    first
    | (have i₁ := eq854
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq854
    | exact resolve eq854 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq896 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq853
       have i₂ := eq101 x
       grind)
    | exact superpose eq101 eq853
    | exact resolve eq853 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq853
  have eq897 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq896
       have i₂ := eq895
       grind)
    | exact superpose eq895 eq896
    | exact resolve eq896 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895 eq896
  have eq898 : False := by grind
  exact eq898

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation413 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq453 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
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
  have eq454 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq2994 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq454 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq454
    | exact resolve eq454 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq3037 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2994 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2994
    | (have j0 := eq2994 X0 X1
       grind)
    | exact resolve eq2994 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2994
  have eq3047 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq3037 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq3037 X0 X1
       grind)
    | exact superpose eq3037 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq3037 X1 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq3037 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq3037 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq3037 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq13 eq3037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3076 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (σ (k (τ X0) X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0
       have i₂ := eq3037 X1 (τ X0)
       grind)
    | (have i₁ := eq30 X0
       have i₂ := eq3037 (τ X0) (τ X0)
       grind)
    | exact superpose eq3037 eq30
    | (have j1 := eq3037 X1 (τ X0)
       grind)
    | exact resolve eq30 eq3037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3037
  have eq3083 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3047 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3047
  have eq3084 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3083 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3083
  have eq3086 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3076 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq3076
    | (have j0 := eq3076 X0 X1
       grind)
    | exact resolve eq3076 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3076
  have eq3187 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq3084 X0 X1
       grind)
    | exact superpose eq3084 eq10
    | (have j1 := eq3084 X0 X1
       grind)
    | exact resolve eq10 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3084
  have eq3231 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3187 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq3187
    | (have j0 := eq3187 X0 X1
       grind)
    | exact resolve eq3187 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3187
  have eq3263 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3231 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3231
    | (have j0 := eq3231 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq3231 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3231
  have eq3421 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3263 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq3263
    | (have j0 := eq3263 X0 X1
       grind)
    | exact resolve eq3263 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3263
  have eq3561 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (k (τ (σ x)) y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq453 (σ x) y
       grind)
    | exact superpose eq453 eq16
    | (have j1 := eq453 (σ x) y
       grind)
    | (have r₁ := eq16
       have r₂ := eq453 (M.op (σ x) (σ y)) (M.op x y)
       grind)
    | exact resolve eq16 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq3574 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k (τ (σ x)) y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3561
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq3561
    | exact resolve eq3561 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3561
  have eq3585 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3574
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3574
    | exact resolve eq3574 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3574
  have eq7063 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3086 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3086
    | exact resolve eq3086 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3086
  have eq7174 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7063 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7063
    | (have j0 := eq7063 X0 X1
       grind)
    | exact resolve eq7063 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7063
  have eq7186 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7174 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq7174
    | (have j0 := eq7174 X0 X1
       grind)
    | exact resolve eq7174 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7174
  have eq15458 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3421 x y
       grind)
    | exact superpose eq3421 eq16
    | (have j1 := eq3421 x y
       grind)
    | exact resolve eq16 eq3421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3421
  have eq15564 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq15458
       have i₂ := eq7186 x y
       grind)
    | exact superpose eq7186 eq15458
    | (have j1 := eq7186 x y
       grind)
    | (have r₁ := eq15458
       have r₂ := eq7186 x y
       grind)
    | (have r₁ := eq15458
       have r₂ := eq7186 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq15458
       have r₂ := eq7186 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq15458 eq7186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7186 eq15458
  have eq15567 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq15564
  have eq15568 : x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq15567
  have eq15573 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15568
       grind)
    | exact superpose eq15568 eq16
    | exact resolve eq16 eq15568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15568
  have eq15574 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq15573
       have r₂ := eq22 x
       grind)
    | exact resolve eq15573 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15573
  have eq15576 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15574
       grind)
    | exact superpose eq15574 eq10
    | exact resolve eq10 eq15574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15574
  have eq15640 : x = y ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq15576
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15576
    | exact resolve eq15576 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15576
  have eq15642 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15640
       grind)
    | exact superpose eq15640 eq16
    | exact resolve eq16 eq15640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15640
  have eq15643 : (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq15642
       have r₂ := eq22 x
       grind)
    | exact resolve eq15642 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15642
  have eq15993 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3585
       have i₂ := eq15643
       grind)
    | exact superpose eq15643 eq3585
    | (have r₁ := eq3585
       have r₂ := eq15643
       grind)
    | exact resolve eq3585 eq15643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3585
  have eq15994 : (M.op x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq15643
       grind)
    | exact superpose eq15643 eq10
    | exact resolve eq10 eq15643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16040 : (σ x) = (σ y) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq15993
  have eq16060 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq15994
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq15994
    | exact resolve eq15994 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15994
  have eq16063 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq16060
       grind)
    | exact superpose eq16060 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq16060
       grind)
    | exact resolve eq13 eq16060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16060
  have eq16067 : x = y ∨ (k x y) = (M.op x x) := by grind
  clear eq16063
  have eq16069 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16067
       grind)
    | exact superpose eq16067 eq16
    | exact resolve eq16 eq16067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16067
  have eq16070 : (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq16069
       have r₂ := eq22 x
       grind)
    | exact resolve eq16069 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16069
  have eq16981 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16040
       grind)
    | exact superpose eq16040 eq16
    | exact resolve eq16 eq16040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16040
  have eq17071 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16981
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq16981
    | exact resolve eq16981 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq16981
  have eq17092 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq17071
       have r₂ := eq15643
       grind)
    | exact resolve eq17071 eq15643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17071
  have eq17093 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq17092
       have i₂ := eq16070
       grind)
    | exact superpose eq16070 eq17092
    | exact resolve eq17092 eq16070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16070 eq17092
  have eq17112 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq17093
       grind)
    | exact superpose eq17093 eq11
    | exact resolve eq11 eq17093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17093
  have eq17222 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17112
       grind)
    | exact superpose eq17112 eq16
    | exact resolve eq16 eq17112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17112
  have eq17244 : False := by grind
  exact eq17244

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation413 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq447 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
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
  have eq450 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq473 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq450 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq450
    | (have j0 := eq450 X0 X1
       grind)
    | exact resolve eq450 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq1047 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq473 x y
       grind)
    | exact superpose eq473 eq16
    | (have j1 := eq473 x y
       grind)
    | exact resolve eq16 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq2972 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq447 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq447
    | exact resolve eq447 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq3021 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2972 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2972
    | (have j0 := eq2972 X0 X1
       grind)
    | exact resolve eq2972 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2972
  have eq3026 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq3021 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq3021 X0 X1
       grind)
    | exact superpose eq3021 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq3021 X1 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq3021 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq3021 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq3021 (M.op X1 X0) (M.op X0 X0)
       grind)
    | exact resolve eq13 eq3021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3039 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 (τ X1))) ∨ (σ (k (τ X1) X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1
       have i₂ := eq3021 X0 (τ X1)
       grind)
    | (have i₁ := eq30 X0
       have i₂ := eq3021 (τ X0) (τ X0)
       grind)
    | exact superpose eq3021 eq30
    | (have j1 := eq3021 X0 (τ X1)
       grind)
    | exact resolve eq30 eq3021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3021
  have eq3046 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3026 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3026
  have eq3047 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3046 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3046
  have eq3049 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X1 X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3039 X0 X1
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq3039
    | (have j0 := eq3039 X0 X1
       grind)
    | exact resolve eq3039 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3039
  have eq3097 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq3047 X1 X0
       grind)
    | exact superpose eq3047 eq10
    | (have j1 := eq3047 X1 X0
       grind)
    | exact resolve eq10 eq3047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3047
  have eq3141 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3097 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq3097
    | (have j0 := eq3097 X0 X1
       grind)
    | exact resolve eq3097 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3097
  have eq3173 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3141 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3141
    | (have j0 := eq3141 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq3141 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3141
  have eq3331 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3173 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq3173
    | (have j0 := eq3173 X0 X1
       grind)
    | exact resolve eq3173 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3173
  have eq4214 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3049 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3049
    | exact resolve eq3049 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3049
  have eq4283 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4214 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4214
    | (have j0 := eq4214 X0 X1
       grind)
    | exact resolve eq4214 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4214
  have eq4284 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4283 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq4283
    | (have j0 := eq4283 X0 X1
       grind)
    | exact resolve eq4283 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4283
  have eq10763 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3331 y x
       grind)
    | exact superpose eq3331 eq16
    | (have j1 := eq3331 y x
       grind)
    | exact resolve eq16 eq3331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3331
  have eq10849 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq10763
       have i₂ := eq4284 y x
       grind)
    | exact superpose eq4284 eq10763
    | (have j1 := eq4284 y x
       grind)
    | (have r₁ := eq10763
       have r₂ := eq4284 y x
       grind)
    | (have r₁ := eq10763
       have r₂ := eq4284 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq10763
       have r₂ := eq4284 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq10763 eq4284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4284 eq10763
  have eq10852 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10849
  have eq10853 : x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq10852
  have eq10858 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10853
       grind)
    | exact superpose eq10853 eq16
    | exact resolve eq16 eq10853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10853
  have eq10859 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq10858
       have r₂ := eq22 x
       grind)
    | exact resolve eq10858 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10858
  have eq10861 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq10859
       grind)
    | exact superpose eq10859 eq10
    | exact resolve eq10 eq10859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10859
  have eq10925 : x = y ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10861
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10861
    | exact resolve eq10861 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10861
  have eq10927 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10925
       grind)
    | exact superpose eq10925 eq16
    | exact resolve eq16 eq10925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10925
  have eq10928 : (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq10927
       have r₂ := eq22 x
       grind)
    | exact resolve eq10927 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10927
  have eq10934 : (M.op y y) = (τ (σ (M.op x y))) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq10928
       grind)
    | exact superpose eq10928 eq10
    | exact resolve eq10 eq10928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10998 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10934
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq10934
    | exact resolve eq10934 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10934
  have eq11001 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ (M.op x y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y x
       have i₂ := eq10998
       grind)
    | exact superpose eq10998 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq10998
       grind)
    | exact resolve eq13 eq10998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10998
  have eq12011 : x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have j0 := eq11001 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11001
  have eq12018 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12011
       grind)
    | exact superpose eq12011 eq16
    | exact resolve eq16 eq12011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12011
  have eq12022 : (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq12018
       have r₂ := eq22 x
       grind)
    | exact resolve eq12018 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12018
  have eq12027 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1047
       have i₂ := eq12022
       grind)
    | exact superpose eq12022 eq1047
    | exact resolve eq1047 eq12022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047 eq12022
  have eq12035 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq12027
  have eq12041 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12035
       have i₂ := eq10928
       grind)
    | exact superpose eq10928 eq12035
    | exact resolve eq12035 eq10928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10928 eq12035
  have eq12045 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq12041
       have r₂ := eq16
       grind)
    | exact resolve eq12041 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12041
  have eq12048 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12045
       grind)
    | exact superpose eq12045 eq16
    | exact resolve eq16 eq12045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12049 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq12045
       grind)
    | exact superpose eq12045 eq10
    | exact resolve eq10 eq12045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12045
  have eq12128 : x = y := by
    first
    | (have i₁ := eq12049
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12049
    | exact resolve eq12049 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12049
  have eq12129 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12048
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq12048
    | exact resolve eq12048 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12048
  have eq12134 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12129
       have i₂ := eq12128
       grind)
    | exact superpose eq12128 eq12129
    | exact resolve eq12129 eq12128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12128 eq12129
  have eq12135 : False := by grind
  exact eq12135

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_pyy_pxy_Equation413 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq106 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq116 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
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
  have eq544 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq116 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq116
    | exact resolve eq116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq574 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq544 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq544
    | (have j0 := eq544 X0 X1
       grind)
    | exact resolve eq544 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq580 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq574 X1 X0
       grind)
    | exact superpose eq574 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq574 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq574 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq574 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq574 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq581 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq574 X1 X0
       grind)
    | exact superpose eq574 eq9
    | (have j1 := eq574 X1 X0
       grind)
    | exact resolve eq9 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq580 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq596 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq595 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq768 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq114 x y
       grind)
    | exact superpose eq114 eq16
    | (have j1 := eq114 x y
       grind)
    | exact resolve eq16 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq775 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq4101 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq581 X0 X1
       grind)
    | exact superpose eq581 eq9
    | (have j1 := eq581 X0 X1
       grind)
    | exact resolve eq9 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq4137 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (σ (k X1 (τ X0))) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0
       have i₂ := eq4101 (τ X0) X1
       grind)
    | exact superpose eq4101 eq30
    | (have j1 := eq4101 (τ X0) X1
       grind)
    | exact resolve eq30 eq4101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4101
  have eq4148 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 (τ X0))) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4137 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4137
    | (have j0 := eq4137 X0 X1
       grind)
    | exact resolve eq4137 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4137
  have eq4154 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4148 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq4148
    | (have j0 := eq4148 X0 X1
       grind)
    | exact resolve eq4148 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq4148
  have eq4203 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0
       have i₂ := eq4154 (σ X0) X1
       grind)
    | exact superpose eq4154 eq22
    | (have j1 := eq4154 (σ X0) X1
       grind)
    | exact resolve eq22 eq4154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4154
  have eq4216 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4203 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4203
    | (have j0 := eq4203 X0 X1
       grind)
    | exact resolve eq4203 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4203
  have eq4223 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4216 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4216
    | (have j0 := eq4216 X0 X1
       grind)
    | exact resolve eq4216 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4216
  have eq4228 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4223 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4223
    | (have j0 := eq4223 X0 X1
       grind)
    | exact resolve eq4223 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4223
  have eq6109 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq768
       have i₂ := eq596 y x
       grind)
    | exact superpose eq596 eq768
    | (have j1 := eq596 y x
       grind)
    | (have r₁ := eq768
       have r₂ := eq596 y x
       grind)
    | (have r₁ := eq768
       have r₂ := eq596 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq768
       have r₂ := eq596 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq768 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq6110 : x = y ∨ (σ x) = (σ y) ∨ (k x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6109
  have eq16554 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6110
       grind)
    | exact superpose eq6110 eq16
    | exact resolve eq16 eq6110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6110
  have eq16555 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16554
       have r₂ := eq22 x
       grind)
    | exact resolve eq16554 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16554
  have eq16562 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq775 x y
       have i₂ := eq16555
       grind)
    | exact superpose eq16555 eq775
    | (have j0 := eq775 x y
       grind)
    | exact resolve eq775 eq16555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775 eq16555
  have eq16573 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq16562
  have eq16577 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16573
       grind)
    | exact superpose eq16573 eq16
    | exact resolve eq16 eq16573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16573
  have eq16606 : (σ y) ≠ (σ y) ∨ (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq16577
       have i₂ := eq574 x y
       grind)
    | exact superpose eq574 eq16577
    | (have j1 := eq574 x y
       grind)
    | (have r₁ := eq16577
       have r₂ := eq574 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq16577
       have r₂ := eq574 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq16577
       have r₂ := eq574 (σ y) (σ (M.op y y))
       grind)
    | exact resolve eq16577 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq16577
  have eq16607 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (k x y)) ∨ x = y := by grind
  clear eq16606
  have eq16615 : x = y ∨ (σ (M.op x y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq4228 y x
       grind)
    | (have r₁ := eq16607
       have r₂ := eq4228 y x
       grind)
    | (have r₁ := eq16607
       have r₂ := eq4228 (σ y) (σ (M.op y y))
       grind)
    | (have r₁ := eq16607
       have r₂ := eq4228 (σ (M.op y y)) (σ y)
       grind)
    | exact resolve eq16607 eq4228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4228 eq16607
  have eq16616 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16615
       grind)
    | exact superpose eq16615 eq16
    | exact resolve eq16 eq16615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16615
  have eq16617 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq16616
       have r₂ := eq22 x
       grind)
    | exact resolve eq16616 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16616
  have eq16770 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq16617
       grind)
    | exact superpose eq16617 eq10
    | exact resolve eq10 eq16617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16617
  have eq16832 : x = y ∨ (σ (M.op x y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq16770
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16770
    | exact resolve eq16770 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16770
  have eq16834 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16832
       grind)
    | exact superpose eq16832 eq16
    | exact resolve eq16 eq16832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16832
  have eq16835 : (σ (M.op x y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq16834
       have r₂ := eq22 x
       grind)
    | exact resolve eq16834 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16834
  have eq16841 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq768
       have i₂ := eq16835
       grind)
    | exact superpose eq16835 eq768
    | (have r₁ := eq768
       have r₂ := eq16835
       grind)
    | exact resolve eq768 eq16835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq16889 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq16841
  have eq16928 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16889
       grind)
    | exact superpose eq16889 eq16
    | exact resolve eq16 eq16889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16931 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9 (σ y) (σ x)
       have i₂ := eq16889
       grind)
    | exact superpose eq16889 eq9
    | exact resolve eq9 eq16889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16932 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq16889
       grind)
    | exact superpose eq16889 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq16889
       grind)
    | exact resolve eq13 eq16889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16889
  have eq16936 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq16932
  have eq16937 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq16936
  have eq16944 : (k (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16937
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq16937
    | exact resolve eq16937 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16937
  have eq16945 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by
    first
    | (have i₁ := eq16931
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq16931
    | exact resolve eq16931 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16931
  have eq16950 : (σ (k x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16944
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq16944
    | exact resolve eq16944 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16944
  have eq16952 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16950
       have i₂ := eq16835
       grind)
    | exact superpose eq16835 eq16950
    | exact resolve eq16950 eq16835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16835 eq16950
  have eq17700 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq16952
       grind)
    | exact superpose eq16952 eq10
    | exact resolve eq10 eq16952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16952
  have eq17762 : x = y ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq17700
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17700
    | exact resolve eq17700 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17700
  have eq17764 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17762
       grind)
    | exact superpose eq17762 eq16
    | exact resolve eq16 eq17762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17762
  have eq17771 : (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq17764
       have r₂ := eq22 x
       grind)
    | exact resolve eq17764 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17764
  have eq17803 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ (M.op x y))))) := by
    first
    | (have i₁ := eq106 y
       have i₂ := eq17771
       grind)
    | exact superpose eq17771 eq106
    | exact resolve eq106 eq17771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq17826 : (M.op y y) = (τ (σ (M.op x y))) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq17771
       grind)
    | exact superpose eq17771 eq10
    | exact resolve eq10 eq17771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17888 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq17826
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq17826
    | exact resolve eq17826 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17826
  have eq23924 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16945
       grind)
    | exact superpose eq16945 eq16
    | exact resolve eq16 eq16945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23929 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by
    first
    | (have i₁ := eq22 y
       have i₂ := eq16945
       grind)
    | exact superpose eq16945 eq22
    | exact resolve eq22 eq16945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16945
  have eq24004 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by
    first
    | (have i₁ := eq23929
       have i₂ := eq17771
       grind)
    | exact superpose eq17771 eq23929
    | exact resolve eq23929 eq17771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23929
  have eq24009 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by
    first
    | (have i₁ := eq23924
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq23924
    | exact resolve eq23924 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23924
  have eq24032 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by
    first
    | (have i₁ := eq24004
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq24004
    | exact resolve eq24004 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24004
  have eq24036 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op x y)))) ∨ (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq24009
       have i₂ := eq17771
       grind)
    | exact superpose eq17771 eq24009
    | exact resolve eq24009 eq17771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24009
  have eq24038 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq24032
       have i₂ := eq17771
       grind)
    | exact superpose eq17771 eq24032
    | exact resolve eq24032 eq17771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24032
  have eq24039 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op x y)))) := by
    first
    | (have r₁ := eq24038
       have r₂ := eq24036
       grind)
    | exact resolve eq24038 eq24036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24036 eq24038
  have eq24076 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq17803
       have i₂ := eq24039
       grind)
    | exact superpose eq24039 eq17803
    | exact resolve eq17803 eq24039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17803 eq24039
  have eq24109 : (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq24076
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq24076
    | exact resolve eq24076 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24076
  have eq24128 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24109
       have i₂ := eq17888
       grind)
    | exact superpose eq17888 eq24109
    | exact resolve eq24109 eq17888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17888 eq24109
  have eq24166 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16928
       have i₂ := eq24128
       grind)
    | exact superpose eq24128 eq16928
    | (have r₁ := eq16928
       have r₂ := eq24128
       grind)
    | exact resolve eq16928 eq24128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16928
  have eq24215 : (σ x) = (σ y) := by grind
  clear eq24166
  have eq24251 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24215
       grind)
    | exact superpose eq24215 eq16
    | exact resolve eq16 eq24215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24257 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq22 y
       have i₂ := eq24215
       grind)
    | exact superpose eq24215 eq22
    | exact resolve eq22 eq24215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24322 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq24257
       have i₂ := eq17771
       grind)
    | exact superpose eq17771 eq24257
    | exact resolve eq24257 eq17771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17771 eq24257
  have eq24328 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq24251
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq24251
    | exact resolve eq24251 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24251
  have eq24333 : (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq24322
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq24322
    | exact resolve eq24322 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24322
  have eq24336 : (σ y) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq24328
       have i₂ := eq24128
       grind)
    | exact superpose eq24128 eq24328
    | exact resolve eq24328 eq24128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24328
  have eq24341 : (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq24333
       have i₂ := eq24128
       grind)
    | exact superpose eq24128 eq24333
    | exact resolve eq24333 eq24128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24128 eq24333
  have eq24344 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq24336
       have i₂ := eq24215
       grind)
    | exact superpose eq24215 eq24336
    | exact resolve eq24336 eq24215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24336
  have eq24348 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq24341
       have i₂ := eq24215
       grind)
    | exact superpose eq24215 eq24341
    | exact resolve eq24341 eq24215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24215 eq24341
  have eq24353 : False := by grind
  exact eq24353

/-- `Equation4167`: `x ◇ y = ((y ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation4167 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4167 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4167.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq270 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq270 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq273 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq271 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq271 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq271 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq288 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq273 (σ X0)
       grind)
    | exact superpose eq273 eq15
    | exact resolve eq15 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq307 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq288 X0
       have i₂ := eq273 X0
       grind)
    | exact superpose eq273 eq288
    | exact resolve eq288 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273 eq288
  have eq350 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq307 X0
       grind)
    | exact superpose eq307 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq307 X0
       grind)
    | exact superpose eq307 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq354 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq350 X0 X1
       have j1 := eq351 X0 X1
       grind)
    | (have r₁ := eq350 X0 X1
       have r₂ := eq351 X0 X1
       grind)
    | exact resolve eq350 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350 eq351
  have eq466 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq354 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq354
    | exact resolve eq354 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq483 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq354 y (σ x)
       grind)
    | exact superpose eq354 eq16
    | (have j1 := eq354 y (σ x)
       grind)
    | exact resolve eq16 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq490 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq483
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq483
    | exact resolve eq483 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq508 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq466 X0 X1
       grind)
    | exact superpose eq466 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq466 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq466 X0 X1
       grind)
    | exact resolve eq13 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq518 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq508 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq527 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq518 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq518 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq518 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq552 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq527 X1 (τ X0)
       grind)
    | exact superpose eq527 eq17
    | (have j1 := eq527 X1 (τ X0)
       grind)
    | exact resolve eq17 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq558 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq527 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq835 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq552 X1 (τ X0)
       grind)
    | exact superpose eq552 eq18
    | (have j1 := eq552 X1 (τ X0)
       grind)
    | exact resolve eq18 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq552
  have eq842 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq835 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq835
    | (have j0 := eq835 X0 X1
       grind)
    | exact resolve eq835 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq857 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq842 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq842
    | (have j0 := eq842 X0 X1
       grind)
    | exact resolve eq842 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq860 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq857 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq857
    | (have j0 := eq857 X0 X1
       grind)
    | exact resolve eq857 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq919 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq860 X0 X1
       have i₂ := eq527 X0 X1
       grind)
    | exact superpose eq527 eq860
    | (have j0 := eq860 X1 X0
       have j1 := eq527 X1 X0
       grind)
    | exact resolve eq860 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq860
  have eq986 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq919 X0 X1
       have j1 := eq558 X0 X1
       grind)
    | (have r₁ := eq919 X0 X1
       have r₂ := eq558 X0 X1
       grind)
    | exact resolve eq919 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq919
  have eq1028 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq986 X1 (σ X0)
       grind)
    | exact superpose eq986 eq22
    | (have j1 := eq986 X1 (σ X0)
       grind)
    | exact resolve eq22 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq986
  have eq1068 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1028 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1028
    | (have j0 := eq1028 X0 X1
       grind)
    | exact resolve eq1028 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028
  have eq1088 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1068 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1068
    | (have j0 := eq1068 X0 X1
       grind)
    | exact resolve eq1068 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1333 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1088 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1088
    | exact resolve eq1088 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq1396 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1333 x y
       grind)
    | exact superpose eq1333 eq16
    | (have j1 := eq1333 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1333 x y
       grind)
    | exact resolve eq16 eq1333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1333
  have eq1414 : y = (k x y) := by grind
  clear eq1396
  have eq2622 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq490
       have i₂ := eq466 y x
       grind)
    | exact superpose eq466 eq490
    | (have j1 := eq466 y x
       grind)
    | exact resolve eq490 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2623 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq2622
  have eq2624 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq2623
       have i₂ := eq1414
       grind)
    | exact superpose eq1414 eq2623
    | exact resolve eq2623 eq1414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2623
  have eq2625 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2624
       have i₂ := eq1414
       grind)
    | exact superpose eq1414 eq2624
    | exact resolve eq2624 eq1414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2624
  have eq2626 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq490
       have i₂ := eq2625
       grind)
    | exact superpose eq2625 eq490
    | exact resolve eq490 eq2625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490 eq2625
  have eq2637 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2626
  have eq2638 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2637
       have i₂ := eq1414
       grind)
    | exact superpose eq1414 eq2637
    | exact resolve eq2637 eq1414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2637
  have eq2639 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2638
  have eq2643 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2639
       grind)
    | exact superpose eq2639 eq16
    | exact resolve eq16 eq2639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2639
  have eq2678 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq2643
       have i₂ := eq466 y x
       grind)
    | exact superpose eq466 eq2643
    | (have j1 := eq466 y x
       grind)
    | exact resolve eq2643 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq2679 : (M.op x y) = (k x y) := by grind
  clear eq2678
  have eq2681 : y = (M.op x y) := by
    first
    | (have i₁ := eq2679
       have i₂ := eq1414
       grind)
    | exact superpose eq1414 eq2679
    | exact resolve eq2679 eq1414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414 eq2679
  have eq2682 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2643
       have i₂ := eq2681
       grind)
    | exact superpose eq2681 eq2643
    | exact resolve eq2643 eq2681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2643 eq2681
  have eq2695 : False := by grind
  exact eq2695

/-- `Equation4167`: `x ◇ y = ((y ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation4167 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4167 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4167.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq172 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq442 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq453 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (τ (M.op X1 X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq442 X0 X1
       have i₂ := eq63 X1
       grind)
    | exact superpose eq63 eq442
    | (have j0 := eq442 X0 X1
       grind)
    | exact resolve eq442 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq459 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq436 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq436
    | (have j0 := eq436 X0 X1
       grind)
    | exact resolve eq436 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq2920 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (M.op (σ X0) (σ X0))) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq459 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq459
    | (have j0 := eq459 (σ X1) (σ X0)
       grind)
    | exact resolve eq459 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3025 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2920 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq2920
    | (have j0 := eq2920 X0 X1
       grind)
    | exact resolve eq2920 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2920
  have eq3517 : ∀ X0 X1 : G, (M.op X1 (σ (σ X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = X1 ∨ (σ (σ (M.op X0 X0))) = (k (σ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq172 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq172
    | (have j0 := eq172 (σ X0) X1
       grind)
    | (have r₁ := eq172 X0 (σ X0)
       have r₂ := eq22 X0
       grind)
    | exact resolve eq172 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq4281 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) ∨ (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 (τ X0))
       have i₂ := eq453 X1 X0
       grind)
    | exact superpose eq453 eq10
    | (have j1 := eq453 X1 X0
       grind)
    | exact resolve eq10 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq4345 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4281 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq4281
    | (have j0 := eq4281 X0 X1
       grind)
    | exact resolve eq4281 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4281
  have eq73694 : ∀ X0 X1 : G, (σ (σ (M.op X1 X1))) = (M.op (σ X0) (σ (σ X1))) ∨ (M.op (σ X0) (σ (σ X1))) = (σ (σ (k X1 (τ X0)))) ∨ (σ X0) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3025 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3025
    | exact resolve eq3025 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3025
  have eq74069 : ∀ X0 X1 : G, (σ (σ (M.op X1 X1))) = (M.op (σ X0) (σ (σ X1))) ∨ (M.op (σ X0) (σ (σ X1))) = (σ (k (σ X1) X0)) ∨ (σ X0) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq73694 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq73694
    | (have j0 := eq73694 X0 X1
       grind)
    | exact resolve eq73694 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq73694
  have eq74719 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ X1) = (σ (σ X0)) ∨ (σ (σ (M.op X0 X0))) = (k (σ (σ X0)) (σ X1)) ∨ (σ (k (σ X0) X1)) = (M.op (σ X1) (σ (σ X0))) ∨ (σ X1) = (σ (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3517 X0 (σ X1)
       have i₂ := eq74069 X1 X0
       grind)
    | exact superpose eq74069 eq3517
    | (have j0 := eq3517 X0 (σ X1)
       have j1 := eq74069 X1 X0
       grind)
    | (have r₁ := eq3517 X1 (σ X0)
       have r₂ := eq74069 X0 X1
       grind)
    | exact resolve eq3517 eq74069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3517 eq74069
  have eq74729 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ X1) = (σ (σ X0)) ∨ (σ (σ (M.op X0 X0))) = (k (σ (σ X0)) (σ X1)) ∨ (σ (k (σ X0) X1)) = (M.op (σ X1) (σ (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq74719 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74719
  have eq74730 : ∀ X0 X1 : G, (σ X1) = (σ (σ X0)) ∨ (σ (σ (M.op X0 X0))) = (k (σ (σ X0)) (σ X1)) ∨ (σ (k (σ X0) X1)) = (M.op (σ X1) (σ (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq74729 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74729
  have eq74746 : ∀ X0 X1 : G, (σ (k (σ X0) X1)) = (M.op (σ X1) (σ (σ X0))) ∨ (σ X1) = (σ (σ X0)) ∨ (σ (σ (M.op X0 X0))) = (σ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq74730 X0 X1
       have i₂ := eq15 (σ X0) X1
       grind)
    | exact superpose eq15 eq74730
    | (have j0 := eq74730 X0 X1
       grind)
    | exact resolve eq74730 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74730
  have eq76060 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (σ (σ (M.op (τ X0) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq74746 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq74746
    | (have j0 := eq74746 (M.op (τ X0) (τ X0)) (k X0 X1)
       grind)
    | exact resolve eq74746 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74746
  have eq76402 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (σ (τ (M.op X0 X0)))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq76060 X0 X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq76060
    | (have j0 := eq76060 X0 X1
       grind)
    | exact resolve eq76060 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76060
  have eq76473 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq76402 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq76402
    | (have j0 := eq76402 X0 X1
       grind)
    | exact resolve eq76402 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76402
  have eq76642 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76473 (τ X1) (τ X0)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq76473
    | (have j0 := eq76473 (M.op (τ X0) (τ X0)) (τ (k X0 X1))
       grind)
    | exact resolve eq76473 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq77080 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76642 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq76642
    | (have j0 := eq76642 X0 X1
       grind)
    | exact resolve eq76642 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76642
  have eq77253 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq77080 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq77080
    | (have j0 := eq77080 X0 X1
       grind)
    | exact resolve eq77080 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77080
  have eq77410 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq77253 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq77253
    | (have j0 := eq77253 X0 X1
       grind)
    | exact resolve eq77253 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77253
  have eq77557 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) = (M.op X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq77410 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq77410
    | (have j0 := eq77410 X0 X1
       grind)
    | exact resolve eq77410 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77410
  have eq77673 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X0))) ∨ (k X0 X1) = (M.op X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq77557 X0 X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq77557
    | (have j0 := eq77557 X0 X1
       grind)
    | exact resolve eq77557 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77557
  have eq77745 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq77673 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq77673
    | (have j0 := eq77673 X0 X1
       grind)
    | exact resolve eq77673 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77673
  have eq77791 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq77745 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq77745
    | (have j0 := eq77745 X0 X1
       grind)
    | exact resolve eq77745 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77745
  have eq77820 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq77791 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq77791
    | (have j0 := eq77791 X0 X1
       grind)
    | exact resolve eq77791 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77791
  have eq78151 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = (k (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq77820 (τ X1) X0
       grind)
    | exact superpose eq77820 eq18
    | (have j1 := eq77820 (τ X1) X0
       grind)
    | exact resolve eq18 eq77820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq77820
  have eq78604 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = (τ (M.op X1 X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq78151 X0 X1
       have i₂ := eq63 X1
       grind)
    | exact superpose eq63 eq78151
    | (have j0 := eq78151 X0 X1
       grind)
    | exact resolve eq78151 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq78151
  have eq79762 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) ∨ (k (τ X0) X1) = (τ (M.op X0 X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 (τ X0))
       have i₂ := eq78604 X1 X0
       grind)
    | exact superpose eq78604 eq10
    | (have j1 := eq78604 X1 X0
       grind)
    | exact resolve eq10 eq78604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78604
  have eq79883 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 X0)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79762 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq79762
    | (have j0 := eq79762 X0 X1
       grind)
    | exact resolve eq79762 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq79762
  have eq80608 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op X1 (τ X0)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq79883 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79883
  have eq80619 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq80608 X0 X1
       have j1 := eq4345 X0 X1
       grind)
    | (have r₁ := eq80608 X0 X1
       have r₂ := eq4345 X0 X1
       grind)
    | (have r₁ := eq80608 X0 X1
       have r₂ := eq4345 (M.op X0 X0) (M.op X1 (τ X0))
       grind)
    | exact resolve eq80608 eq4345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4345 eq80608
  have eq81728 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq80619 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq80619
    | exact resolve eq80619 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80619
  have eq82363 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq459 X0 X1
       have i₂ := eq81728 X1 X0
       grind)
    | exact superpose eq81728 eq459
    | (have j0 := eq459 X0 X1
       have j1 := eq81728 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq459 eq81728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq82367 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ (M.op X1 X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq76473 X0 X1
       have i₂ := eq81728 X0 X1
       grind)
    | exact superpose eq81728 eq76473
    | (have j0 := eq76473 (M.op X1 X1) (M.op X0 X1)
       have j1 := eq81728 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq76473 eq81728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76473 eq81728
  have eq83866 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq82363 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82363
  have eq84248 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq83866 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83866
  have eq84261 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq84248 X0 X1
       have j1 := eq82367 X0 X1
       grind)
    | (have r₁ := eq84248 X0 X1
       have r₂ := eq82367 X0 X1
       grind)
    | (have r₁ := eq84248 X1 X1
       have r₂ := eq82367 X1 X1
       grind)
    | (have r₁ := eq84248 X0 X1
       have r₂ := eq82367 (M.op X1 X1) (M.op X0 X1)
       grind)
    | exact resolve eq84248 eq82367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82367 eq84248
  have eq89682 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq84261 x y
       grind)
    | exact superpose eq84261 eq16
    | (have j1 := eq84261 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq84261 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq84261 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq84261 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq84261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84261
  have eq89697 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq89682
  have eq90528 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq89697
       grind)
    | exact superpose eq89697 eq10
    | exact resolve eq10 eq89697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89697
  have eq90710 : x = y ∨ x = y := by
    first
    | (have i₁ := eq90528
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq90528
    | exact resolve eq90528 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90528
  have eq90711 : x = y := by grind
  clear eq90710
  have eq90714 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq90711
       grind)
    | exact superpose eq90711 eq16
    | exact resolve eq16 eq90711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90711
  have eq90715 : False := by grind
  exact eq90715
