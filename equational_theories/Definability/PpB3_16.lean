import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyy_x_pxx_pyx_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X2)) X3 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq265 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq265
    | (have j0 := eq265 (σ X0)
       grind)
    | exact resolve eq265 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (σ X0)
       have i₂ := eq265 (σ X0)
       grind)
    | exact superpose eq265 eq28
    | (have j1 := eq265 (σ X0)
       grind)
    | exact resolve eq28 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq265 (τ X0)
       grind)
    | exact superpose eq265 eq17
    | (have j1 := eq265 (τ X0)
       grind)
    | exact resolve eq17 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq283 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq283
    | (have j0 := eq283 X0
       grind)
    | exact resolve eq283 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq293 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq277 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq277
    | (have j0 := eq277 X0
       grind)
    | exact resolve eq277 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq302 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq266 X0
       have i₂ := eq265 X0
       grind)
    | exact superpose eq265 eq266
    | (have j0 := eq266 X0
       have j1 := eq265 (σ X0)
       grind)
    | exact resolve eq266 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq266
  have eq356 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq288 X0
       grind)
    | exact superpose eq288 eq10
    | (have j1 := eq288 X0
       grind)
    | exact resolve eq10 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq396 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq356 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq396 (σ X0)
       have i₂ := eq28 X0 (σ X0)
       grind)
    | exact superpose eq28 eq396
    | (have j0 := eq396 (σ X0)
       grind)
    | exact resolve eq396 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq407 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq406 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq406
    | (have j0 := eq406 X0
       grind)
    | exact resolve eq406 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq410 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq407 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq407
    | (have j0 := eq407 X0
       grind)
    | exact resolve eq407 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq444 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq480 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X0 X1 X2 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq488 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq480 X0 X1 x
       grind)
    | exact superpose eq480 eq9
    | exact resolve eq9 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq501 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq488 (M.op X0 X1) X2
       have i₂ := eq480 X0 X1 X1
       grind)
    | exact superpose eq480 eq488
    | exact resolve eq488 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq488 X0 (M.op X0 X1)
       have i₂ := eq480 X0 X0 X1
       grind)
    | exact superpose eq480 eq488
    | exact resolve eq488 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq488 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq488 X0 (M.op X0 X0)
       grind)
    | exact superpose eq488 eq488
    | exact resolve eq488 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq503 X0
       grind)
    | exact superpose eq503 eq12
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq503 X0
       grind)
    | exact resolve eq12 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq524 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq522 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq531 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq524 (σ X0)
       grind)
    | exact superpose eq524 eq28
    | exact resolve eq28 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq524 (τ X0)
       grind)
    | exact superpose eq524 eq17
    | exact resolve eq17 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq536 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq536
    | exact resolve eq536 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq546 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq531 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq531
    | exact resolve eq531 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq563 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq541 (τ X0)
       grind)
    | exact superpose eq541 eq17
    | exact resolve eq17 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq541
  have eq568 : ∀ X0 : G, (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq563 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq563
    | exact resolve eq563 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq598 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (τ (M.op (σ (σ X0)) (σ (σ X0))))
       have i₂ := eq546 (σ X0)
       grind)
    | exact superpose eq546 eq28
    | exact resolve eq28 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq619 : ∀ X0 : G, (k X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq598 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq598
    | exact resolve eq598 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq692 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq501 (M.op X0 X0) (M.op X0 X0) X1
       have i₂ := eq488 X0 (M.op X0 X0)
       grind)
    | exact superpose eq488 eq501
    | exact resolve eq501 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq501 (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq501 X0 X1 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq501 eq501
    | exact resolve eq501 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq501 X0 X0 (M.op X0 X1)
       have i₂ := eq502 X0 X1
       grind)
    | exact superpose eq502 eq501
    | exact resolve eq501 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq725 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = (M.op (M.op (M.op X0 X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq693 X0 X1 X2
       have i₂ := eq480 (M.op X0 X0) X1 X1
       grind)
    | exact superpose eq480 eq693
    | exact resolve eq693 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq726 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq692 X0 X1
       have i₂ := eq480 X0 X0 X0
       grind)
    | exact superpose eq480 eq692
    | exact resolve eq692 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq735 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (M.op (M.op (M.op X0 X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq725 X0 X1 X2
       have i₂ := eq480 X0 X0 X0
       grind)
    | exact superpose eq480 eq725
    | exact resolve eq725 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq770 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq726 X0 X2
       have i₂ := eq726 X0 X1
       grind)
    | (have i₁ := eq726 X1 X1
       have i₂ := eq726 X1 X1
       grind)
    | exact superpose eq726 eq726
    | exact resolve eq726 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq779 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq501 X0 X0 X2
       have i₂ := eq726 X0 X1
       grind)
    | (have i₁ := eq501 X1 X1 X2
       have i₂ := eq726 X1 X1
       grind)
    | exact superpose eq726 eq501
    | exact resolve eq501 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq781 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq488 X0 X0
       have i₂ := eq726 X0 X1
       grind)
    | (have i₁ := eq488 X1 X1
       have i₂ := eq726 X1 X1
       grind)
    | exact superpose eq726 eq488
    | exact resolve eq488 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq782 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq502 X0 X2
       have i₂ := eq726 X0 X1
       grind)
    | (have i₁ := eq502 X1 X1
       have i₂ := eq726 X1 X1
       grind)
    | exact superpose eq726 eq502
    | exact resolve eq502 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502 eq726
  have eq837 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) X2) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq480 (M.op (M.op X0 X1) X1) X2 X0
       have i₂ := eq781 X0 X1
       grind)
    | exact superpose eq781 eq480
    | exact resolve eq480 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq843 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X2) X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq837 X0 X1 X2
       have i₂ := eq480 (M.op X0 X1) X1 X1
       grind)
    | exact superpose eq480 eq837
    | exact resolve eq837 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq852 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) X1) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq843 X0 X1 X2
       have i₂ := eq480 X0 X1 X1
       grind)
    | exact superpose eq480 eq843
    | exact resolve eq843 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq858 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq852 X0 X1 X2
       have i₂ := eq488 X0 X1
       grind)
    | exact superpose eq488 eq852
    | exact resolve eq852 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq863 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op (M.op (M.op X0 X2) X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq770 (M.op X0 X2) X2 X3
       have i₂ := eq770 X0 X2 X1
       grind)
    | (have i₁ := eq770 (M.op X0 X2) X2 X3
       have i₂ := eq770 X0 X1 X2
       grind)
    | exact superpose eq770 eq770
    | exact resolve eq770 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1023 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X2) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq782 (M.op (M.op X0 X0) X1) X2 X1
       have i₂ := eq488 X0 X1
       grind)
    | exact superpose eq488 eq782
    | exact resolve eq782 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1061 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1023 X0 X1 x
       have i₂ := eq501 X0 X1 x
       grind)
    | exact superpose eq501 eq1023
    | exact resolve eq1023 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq1721 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X2) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq779 X0 X1 X1
       have i₂ := eq770 (M.op X0 X1) X1 X2
       grind)
    | (have i₁ := eq779 X0 X1 X1
       have i₂ := eq770 (M.op X0 X1) X2 X1
       grind)
    | exact superpose eq770 eq779
    | exact resolve eq779 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1764 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (M.op (M.op (M.op (σ X0) X1) X1) X2) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq546 X0
       have i₂ := eq779 (σ X0) X1 X2
       grind)
    | exact superpose eq779 eq546
    | exact resolve eq546 eq779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq2361 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq858 X0 X1 X1
       have i₂ := eq770 (M.op X0 X1) X1 X2
       grind)
    | (have i₁ := eq858 X0 X1 X1
       have i₂ := eq770 (M.op X0 X1) X2 X1
       grind)
    | exact superpose eq770 eq858
    | exact resolve eq858 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq4718 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq62 X0 X1 x X3
       have i₂ := eq480 X0 X1 x
       grind)
    | exact superpose eq480 eq62
    | exact resolve eq62 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq4782 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq501 (M.op (M.op X0 X0) X1) X0 (M.op (M.op X0 X0) X1)
       have i₂ := eq4718 X0 X1 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq4718 eq501
    | exact resolve eq501 eq4718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4872 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = (M.op (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4782 X0 X1
       have i₂ := eq480 (M.op X0 X0) X1 X1
       grind)
    | exact superpose eq480 eq4782
    | exact resolve eq4782 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4782
  have eq4925 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (M.op (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4872 X0 X1
       have i₂ := eq480 X0 X0 X0
       grind)
    | exact superpose eq480 eq4872
    | exact resolve eq4872 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4872
  have eq6141 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X3) X3) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X2) X0) (M.op (M.op (M.op (M.op X0 X0) X1) X2) X0)) (M.op (M.op (M.op (M.op X0 X0) X1) X2) X0)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq735 (M.op (M.op (M.op (M.op X0 X0) X1) X2) X0) X2 X3
       have i₂ := eq4718 X0 X1 X2
       grind)
    | exact superpose eq4718 eq735
    | exact resolve eq735 eq4718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4718
  have eq6271 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X2) X3) X3) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1721 (M.op (M.op X0 X0) X0) X1 X3
       have i₂ := eq735 X0 X1 X2
       grind)
    | (have i₁ := eq1721 (M.op (M.op X0 X1) X2) X2 X2
       have i₂ := eq735 X0 X1 X2
       grind)
    | exact superpose eq735 eq1721
    | exact resolve eq1721 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6442 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X2) X3) X3) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6271 X0 X1 X2 X3
       have i₂ := eq480 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq480 eq6271
    | exact resolve eq6271 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6271
  have eq6510 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X3) X3) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X2) (M.op (M.op (M.op X0 X0) X1) X2)) (M.op (M.op (M.op X0 X0) X1) X2)) X0) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6141 X0 X1 X2 X3
       have i₂ := eq735 (M.op (M.op (M.op X0 X0) X1) X2) X0 (M.op (M.op (M.op (M.op X0 X0) X1) X2) X0)
       grind)
    | exact superpose eq735 eq6141
    | exact resolve eq6141 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6141
  have eq6574 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X2) X3) X3) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6442 X0 X1 X2 X3
       have i₂ := eq1061 (M.op X0 X0) X0
       grind)
    | exact superpose eq1061 eq6442
    | exact resolve eq6442 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061 eq6442
  have eq6608 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X3) X3) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1)) X2) X0) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6510 X0 X1 X2 X3
       have i₂ := eq735 (M.op (M.op X0 X0) X1) X2 (M.op (M.op (M.op X0 X0) X1) X2)
       grind)
    | exact superpose eq735 eq6510
    | exact resolve eq6510 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6510
  have eq6632 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X2) X3) X3) X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6574 X0 X1 X2 X3
       have i₂ := eq782 X0 X0 X0
       grind)
    | exact superpose eq782 eq6574
    | exact resolve eq6574 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782 eq6574
  have eq6655 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X3) X3) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) X1) X2) X0) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6608 X0 X1 X2 X3
       have i₂ := eq735 (M.op X0 X0) X1 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq735 eq6608
    | exact resolve eq6608 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6608
  have eq6667 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X3) X3) = (M.op (M.op (M.op (M.op X0 X1) X2) X0) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6655 X0 X1 X2 X3
       have i₂ := eq488 X0 (M.op X0 X0)
       grind)
    | exact superpose eq488 eq6655
    | exact resolve eq6655 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6655
  have eq6670 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X2) X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6667 X0 X1 X2 x
       have i₂ := eq501 X0 X1 x
       grind)
    | exact superpose eq501 eq6667
    | exact resolve eq6667 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501 eq6667
  have eq6785 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X0) X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq770 (M.op (M.op (M.op X0 X1) X2) X0) X2 X3
       have i₂ := eq6670 X0 X1 X2
       grind)
    | exact superpose eq6670 eq770
    | exact resolve eq770 eq6670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6670
  have eq7398 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X2) = (M.op (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4925 X0 X1
       have i₂ := eq735 X0 X1 X2
       grind)
    | (have i₁ := eq4925 X2 X2
       have i₂ := eq735 X2 X2 X2
       grind)
    | exact superpose eq735 eq4925
    | exact resolve eq4925 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq4925
  have eq10783 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X0 X2)) = (M.op (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7398 X0 X1 (M.op X0 X2)
       have i₂ := eq480 X0 X1 X2
       grind)
    | exact superpose eq480 eq7398
    | exact resolve eq7398 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7398
  have eq20388 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq444 X0 X1
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq444 X0 X1
       grind)
    | exact superpose eq444 eq13
    | (have j0 := eq13 (σ X0) (σ X0)
       have j1 := eq444 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq444 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq444 X0 X0
       grind)
    | exact resolve eq13 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20508 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (M.op (σ X0) (σ X1)) X2) X2) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq488 (σ X1) X2
       have i₂ := eq444 X0 X1
       grind)
    | (have i₁ := eq488 (σ X1) X1
       have i₂ := eq444 X1 X1
       grind)
    | exact superpose eq444 eq488
    | (have j1 := eq444 X0 X1
       grind)
    | exact resolve eq488 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20531 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq444 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq20537 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq20388 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20388
  have eq20562 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20537 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq20537
    | (have j0 := eq20537 X0 X1
       grind)
    | exact resolve eq20537 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20537
  have eq20577 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq20562 X0 X1
       have j1 := eq20531 X1 X0
       grind)
    | (have r₁ := eq20562 X1 X1
       have r₂ := eq20531 X0 X1
       grind)
    | (have r₁ := eq20562 X1 X1
       have r₂ := eq20531 X0 X1
       grind)
    | exact resolve eq20562 eq20531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20531 eq20562
  have eq41852 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq20577 (M.op X0 X0) X0
       have i₂ := eq524 X0
       grind)
    | exact superpose eq524 eq20577
    | (have j0 := eq20577 (M.op X0 X0) X0
       grind)
    | exact resolve eq20577 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq42033 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq20577 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20577
  have eq42191 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (M.op (σ X0) (σ X0)) (σ X1)) (M.op (σ X0) X2)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20508 X0 X1 (M.op (σ X0) X2)
       have i₂ := eq480 (σ X0) (σ X1) X2
       grind)
    | exact superpose eq480 eq20508
    | (have j0 := eq20508 X0 X1 X2
       grind)
    | exact resolve eq20508 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480 eq20508
  have eq136187 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6785 X0 X1 X0 X2
       have i₂ := eq863 (M.op X0 X1) X0 X2 X3
       grind)
    | (have i₁ := eq6785 X3 X1 X2 X3
       have i₂ := eq863 (M.op X3 X1) X1 X2 X3
       grind)
    | exact superpose eq863 eq6785
    | exact resolve eq6785 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863 eq6785
  have eq420570 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq697 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq41852 X0
       grind)
    | exact superpose eq41852 eq697
    | (have j1 := eq41852 X0
       grind)
    | exact resolve eq697 eq41852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420819 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq41852 eq420570
    | (have j0 := eq420570 X0
       have j1 := eq41852 X0
       grind)
    | exact resolve eq420570 eq41852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41852 eq420570
  have eq420867 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq302 eq420819
    | (have j0 := eq420819 X0
       have j1 := eq302 X0
       grind)
    | exact resolve eq420819 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302 eq420819
  have eq420868 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq420867 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420867
  have eq451806 : ∀ X0 X1 : G, (σ X1) = (M.op (M.op (M.op (σ X0) (σ X0)) (σ X1)) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42191 X0 X1 x
       have i₂ := eq10783 (σ X0) (σ X1) x
       grind)
    | exact superpose eq10783 eq42191
    | (have j0 := eq42191 X0 X1 x
       grind)
    | exact resolve eq42191 eq10783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10783 eq42191
  have eq452085 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X1)) = (M.op (M.op (M.op (M.op (σ X0) (σ X1)) X2) X2) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6632 (M.op (σ X1) (σ X1)) (σ X0) (σ X1) X2
       have i₂ := eq451806 X1 X0
       grind)
    | exact superpose eq451806 eq6632
    | (have j1 := eq451806 X1 X0
       grind)
    | exact resolve eq6632 eq451806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6632 eq451806
  have eq452530 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq452085 X0 X1 x
       have i₂ := eq2361 (σ X0) (σ X1) x
       grind)
    | exact superpose eq2361 eq452085
    | (have j0 := eq452085 X0 X1 x
       grind)
    | exact resolve eq452085 eq2361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2361 eq452085
  have eq452710 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq452530 X0 X1
       have j1 := eq42033 X1 X0
       grind)
    | (have r₁ := eq452530 X1 X1
       have r₂ := eq42033 X1 X1
       grind)
    | (have r₁ := eq452530 X1 X0
       have r₂ := eq42033 X0 X1
       grind)
    | exact resolve eq452530 eq42033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42033 eq452530
  have eq452766 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq452710 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452710
  have eq480719 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq452766 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq452766
    | (have j0 := eq452766 (τ X1) (τ X0)
       grind)
    | exact resolve eq452766 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480885 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq480719 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq480719
    | (have j0 := eq480719 X0 X1
       grind)
    | exact resolve eq480719 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480719
  have eq480916 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq480885 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq480885
    | (have j0 := eq480885 X0 X1
       grind)
    | exact resolve eq480885 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480885
  have eq480929 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq480916 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq480916
    | (have j0 := eq480916 X0 X1
       grind)
    | exact resolve eq480916 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480916
  have eq480936 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq480929 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq480929
    | (have j0 := eq480929 X0 X1
       grind)
    | exact resolve eq480929 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480929
  have eq480943 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq480936 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq480936
    | (have j0 := eq480936 X0 X1
       grind)
    | exact resolve eq480936 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480936
  have eq481004 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq452766 X0 X1
       have i₂ := eq480943 X1 X0
       grind)
    | exact superpose eq480943 eq452766
    | (have j0 := eq452766 X0 X1
       have j1 := eq480943 (σ X1) (σ X0)
       grind)
    | exact resolve eq452766 eq480943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452766
  have eq483665 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq420868 eq293
    | (have j0 := eq293 X0
       have j1 := eq420868 X0
       grind)
    | exact resolve eq293 eq420868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq484012 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq420868 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420868
  have eq484076 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq483665 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq483665
    | (have j0 := eq483665 X0
       grind)
    | exact resolve eq483665 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483665
  have eq484189 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq484076 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq484076
    | (have j0 := eq484076 (τ X0)
       grind)
    | exact resolve eq484076 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq484205 : ∀ X0 : G, (k X0 (τ (σ X0))) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq546 X0
       have i₂ := eq484076 X0
       grind)
    | exact superpose eq484076 eq546
    | (have j1 := eq484076 X0
       grind)
    | exact resolve eq546 eq484076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq484207 : ∀ X0 : G, (k X0 (τ (τ (σ (σ X0))))) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq619 X0
       have i₂ := eq484076 (σ X0)
       grind)
    | exact superpose eq484076 eq619
    | (have j1 := eq484076 (σ X0)
       grind)
    | exact resolve eq619 eq484076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619 eq484076
  have eq484681 : ∀ X0 : G, (k X0 (τ (σ X0))) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq484207 X0
       have i₂ := eq10 (σ X0)
       grind)
    | exact superpose eq10 eq484207
    | (have j0 := eq484207 X0
       grind)
    | exact resolve eq484207 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484207
  have eq484682 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq484205 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq484205
    | (have j0 := eq484205 X0
       grind)
    | exact resolve eq484205 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484205
  have eq484689 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq484189 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq484189
    | (have j0 := eq484189 X0
       grind)
    | exact resolve eq484189 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484189
  have eq484763 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq484681 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq484681
    | (have j0 := eq484681 X0
       grind)
    | exact resolve eq484681 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484681
  have eq484765 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq480943 eq484689
    | (have j0 := eq484689 X0
       have j1 := eq480943 X0 X0
       grind)
    | exact resolve eq484689 eq480943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484689
  have eq484783 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq484763 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq484763
    | (have j0 := eq484763 X0
       grind)
    | exact resolve eq484763 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484763
  have eq485133 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq697 (τ X0) (τ X0)
       have i₂ := eq484765 X0
       grind)
    | exact superpose eq484765 eq697
    | (have j1 := eq484765 X0
       grind)
    | exact resolve eq697 eq484765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484765
  have eq485416 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq484682 eq484783
    | (have j0 := eq484783 X0
       have j1 := eq484682 X0
       grind)
    | exact resolve eq484783 eq484682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484783
  have eq492859 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq485416 X0
       have j1 := eq410 X0
       grind)
    | (have r₁ := eq485416 X0
       have r₂ := eq410 X0
       grind)
    | exact resolve eq485416 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq492924 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq492859 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq492859
    | (have j0 := eq492859 (τ X0)
       grind)
    | exact resolve eq492859 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493059 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq697 (σ X0) (σ X0)
       have i₂ := eq492859 X0
       grind)
    | exact superpose eq492859 eq697
    | (have j1 := eq492859 X0
       grind)
    | exact resolve eq697 eq492859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492859
  have eq493332 : ∀ X0 : G, (M.op X0 X0) = (σ (τ (k X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | exact superpose eq356 eq492924
    | (have j0 := eq492924 X0
       have j1 := eq356 X0
       grind)
    | exact resolve eq492924 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356 eq492924
  have eq493355 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq493332 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq493332
    | (have j0 := eq493332 X0
       grind)
    | exact resolve eq493332 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493332
  have eq493389 : ∀ X0 : G, (k X0 (σ (σ (τ (τ X0))))) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq568 X0
       have i₂ := eq493355 (τ X0)
       grind)
    | exact superpose eq493355 eq568
    | (have j1 := eq493355 (τ X0)
       grind)
    | exact resolve eq568 eq493355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568 eq493355
  have eq493869 : ∀ X0 : G, (k X0 (σ (τ X0))) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq493389 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq493389
    | (have j0 := eq493389 X0
       grind)
    | exact resolve eq493389 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493389
  have eq493949 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq493869 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq493869
    | (have j0 := eq493869 X0
       grind)
    | exact resolve eq493869 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493869
  have eq493968 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq493949 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq493949
    | (have j0 := eq493949 X0
       grind)
    | exact resolve eq493949 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq493949
  have eq493976 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq484682 eq493968
    | (have j0 := eq493968 X0
       have j1 := eq484682 X0
       grind)
    | exact resolve eq493968 eq484682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484682 eq493968
  have eq494059 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq493976 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq493976
    | (have j0 := eq493976 (σ X0)
       grind)
    | exact resolve eq493976 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493976
  have eq494468 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq494059 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq494059
    | (have j0 := eq494059 X0
       grind)
    | exact resolve eq494059 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494059
  have eq613185 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq480943 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq480943 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq480943 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq637819 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq481004 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481004
  have eq637863 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq637819 x y
       grind)
    | exact superpose eq637819 eq16
    | (have j1 := eq637819 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq637819 x y
       grind)
    | exact resolve eq16 eq637819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637819
  have eq638287 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq637863
  have eq638614 : ∀ X0 : G, y = (k y (τ (M.op (M.op (M.op (σ x) (σ x)) X0) X0))) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1764 y (σ x) X0
       have i₂ := eq638287
       grind)
    | exact superpose eq638287 eq1764
    | exact resolve eq1764 eq638287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1764
  have eq638627 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq697 (σ y) (σ x)
       have i₂ := eq638287
       grind)
    | exact superpose eq638287 eq697
    | exact resolve eq697 eq638287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq638955 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq638287 eq638627
    | exact resolve eq638627 eq638287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638287 eq638627
  have eq638964 : y = (k y (τ (σ x))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq638614 x
       have i₂ := eq488 (σ x) x
       grind)
    | exact superpose eq488 eq638614
    | exact resolve eq638614 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488 eq638614
  have eq639028 : y = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq638964
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq638964
    | exact resolve eq638964 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638964
  have eq639050 : y = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq639028
       have r₂ := eq12 y x
       grind)
    | exact resolve eq639028 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639028
  have eq639063 : y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq639050
       have i₂ := eq480943 y x
       grind)
    | exact superpose eq480943 eq639050
    | (have j1 := eq480943 x y
       grind)
    | exact resolve eq639050 eq480943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480943 eq639050
  have eq639263 : ∀ X0 X1 : G, (M.op y x) = (M.op (M.op (M.op (M.op y X0) X1) X1) X0) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq136187 x y x x
       have i₂ := eq639063
       grind)
    | exact superpose eq639063 eq136187
    | exact resolve eq136187 eq639063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639318 : (M.op y x) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq639263 x x
       have i₂ := eq1721 y x x
       grind)
    | exact superpose eq1721 eq639263
    | exact resolve eq639263 eq1721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639263
  have eq643722 : (τ (σ x)) = (M.op y y) ∨ (σ y) = (σ (k y y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq494468 y
       have i₂ := eq638955
       grind)
    | exact superpose eq638955 eq494468
    | (have j0 := eq494468 y
       grind)
    | exact resolve eq494468 eq638955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494468
  have eq643847 : (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq485133 (σ y)
       have i₂ := eq638955
       grind)
    | exact superpose eq638955 eq485133
    | exact resolve eq485133 eq638955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485133 eq638955
  have eq644196 : x = (M.op (τ (σ y)) x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq643847
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq643847
    | exact resolve eq643847 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643847
  have eq644216 : x = (M.op y y) ∨ (σ y) = (σ (k y y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq643722
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq643722
    | exact resolve eq643722 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643722
  have eq644243 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq644196
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq644196
    | exact resolve eq644196 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644196
  have eq644244 : x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq644243
  have eq644255 : x = (M.op y x) ∨ (σ y) = (σ (k y y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq639318 eq644216
    | exact resolve eq644216 eq639318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644216
  have eq644256 : x = (M.op y x) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq644255
  have eq648281 : (σ x) = (σ (k y y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq644244 eq644256
    | exact resolve eq644256 eq644244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644244 eq644256
  have eq648296 : (k y y) = (τ (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq648281
       grind)
    | exact superpose eq648281 eq10
    | exact resolve eq10 eq648281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648281
  have eq648474 : x = (k y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq648296
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq648296
    | exact resolve eq648296 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648296
  have eq648501 : x = (M.op y y) ∨ x = (M.op y x) ∨ y = (k y y) := by
    first
    | (have i₁ := eq648474
       have i₂ := eq613185 y y
       grind)
    | exact superpose eq613185 eq648474
    | (have j1 := eq613185 y y
       grind)
    | exact resolve eq648474 eq613185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613185
  have eq648540 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (k y y) := by
    first
    | exact superpose eq639318 eq648501
    | exact resolve eq648501 eq639318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639318 eq648501
  have eq648541 : x = (M.op y x) ∨ y = (k y y) := by grind
  clear eq648540
  have eq648547 : x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq648474 eq648541
    | exact resolve eq648541 eq648474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648541
  have eq648549 : x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq648547 eq639063
    | exact resolve eq639063 eq648547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639063
  have eq648556 : x = (k x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq648547 eq648474
    | exact resolve eq648474 eq648547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648474
  have eq648604 : ∀ X0 : G, (M.op y y) = (M.op (M.op (M.op x X0) X0) x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1721 y x X0
       have i₂ := eq648547
       grind)
    | exact superpose eq648547 eq1721
    | exact resolve eq1721 eq648547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq648749 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op x X0) X1) X1) X0) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq136187 y x x x
       have i₂ := eq648547
       grind)
    | exact superpose eq648547 eq136187
    | exact resolve eq136187 eq648547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648547
  have eq648808 : (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq648749 x x
       have i₂ := eq1721 x x x
       grind)
    | exact superpose eq1721 eq648749
    | exact resolve eq648749 eq1721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648749
  have eq648875 : x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq648604 x
       have i₂ := eq781 x x
       grind)
    | exact superpose eq781 eq648604
    | exact resolve eq648604 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781 eq648604
  have eq649071 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq493059 y
       have i₂ := eq648875
       grind)
    | exact superpose eq648875 eq493059
    | exact resolve eq493059 eq648875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493059 eq648875
  have eq649335 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by grind
  clear eq649071
  have eq649401 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by grind
  clear eq649335
  have eq649482 : ∀ X0 : G, (M.op x x) = (M.op (M.op y X0) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq770 y x X0
       have i₂ := eq648549
       grind)
    | exact superpose eq648549 eq770
    | exact resolve eq770 eq648549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq648549
  have eq650310 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by grind
  clear eq649401
  have eq654040 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) X0) X1) X1) X0) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq136187 (σ y) (σ x) x x
       have i₂ := eq650310
       grind)
    | exact superpose eq650310 eq136187
    | exact resolve eq136187 eq650310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136187 eq650310
  have eq654102 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq654040 x x
       have i₂ := eq1721 (σ x) x x
       grind)
    | exact superpose eq1721 eq654040
    | exact resolve eq654040 eq1721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1721 eq654040
  have eq701371 : ∀ X0 : G, (M.op (M.op y X0) X0) ≠ (M.op (M.op y X0) X0) ∨ x = (M.op (M.op y X0) X0) ∨ (M.op (M.op y X0) X0) = (k x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13 x x
       have i₂ := eq649482 X0
       grind)
    | exact superpose eq649482 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 (M.op y x) x
       have r₂ := eq649482 x
       grind)
    | exact resolve eq13 eq649482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702148 : ∀ X0 : G, x ≠ (M.op (M.op y X0) X0) ∨ x = (M.op x x) := by
    intro X0
    grind
  clear eq649482
  have eq702150 : ∀ X0 : G, x = (M.op (M.op y X0) X0) ∨ (M.op (M.op y X0) X0) = (k x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq701371 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701371
  have eq702664 : ∀ X0 : G, (M.op (M.op y X0) X0) = (k x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq702150 X0
       grind)
    | (have r₁ := eq702150 X0
       have r₂ := eq702148 X0
       grind)
    | exact resolve eq702150 eq702148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702150
  have eq734986 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq654102
       grind)
    | exact superpose eq654102 eq16
    | exact resolve eq16 eq654102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654102
  have eq735391 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ x = y := by
    first
    | exact superpose eq648808 eq734986
    | exact resolve eq734986 eq648808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648808 eq734986
  have eq735514 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = y ∨ x = (k x x) := by
    first
    | (have i₁ := eq735391
       have i₂ := eq485416 x
       grind)
    | exact superpose eq485416 eq735391
    | (have j1 := eq485416 x
       grind)
    | (have r₁ := eq735391
       have r₂ := eq485416 x
       grind)
    | exact resolve eq735391 eq485416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485416
  have eq735520 : x = (k x x) ∨ x = y := by grind
  clear eq735514
  have eq735528 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq735520 eq648556
    | exact resolve eq648556 eq735520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648556 eq735520
  have eq735547 : x = (k x x) := by
    first
    | (have j1 := eq12 x x
       grind)
    | (have r₁ := eq735528
       have r₂ := eq12 x x
       grind)
    | exact resolve eq735528 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735528
  have eq735549 : ∀ X0 : G, x = (M.op (M.op y X0) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq702664 X0
       have i₂ := eq735547
       grind)
    | exact superpose eq735547 eq702664
    | exact resolve eq702664 eq735547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702664 eq735547
  have eq735564 : x = (M.op x x) := by
    first
    | (have r₁ := eq735549 x
       have r₂ := eq702148 x
       grind)
    | exact resolve eq735549 eq702148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702148 eq735549
  have eq735573 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq735391
       have i₂ := eq735564
       grind)
    | exact superpose eq735564 eq735391
    | exact resolve eq735391 eq735564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735391
  have eq735675 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq484012 x
       have i₂ := eq735564
       grind)
    | exact superpose eq735564 eq484012
    | (have j0 := eq484012 x
       grind)
    | exact resolve eq484012 eq735564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484012
  have eq735946 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq735675
  have eq736114 : x = y := by
    first
    | (have r₁ := eq735573
       have r₂ := eq735946
       grind)
    | exact resolve eq735573 eq735946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735573
  have eq736206 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq736114
       grind)
    | exact superpose eq736114 eq16
    | exact resolve eq16 eq736114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736114
  have eq736215 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq736206
       have i₂ := eq735564
       grind)
    | exact superpose eq735564 eq736206
    | exact resolve eq736206 eq735564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735564 eq736206
  have eq736216 : False := by grind
  exact eq736216

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pyy_pyx_pxy_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq37 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
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
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
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
  have eq66 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X1 X1) = (k (M.op (M.op X0 X1) (M.op X0 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 X1) (M.op X0 X2)) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X0 X1) (M.op X0 X2)) X1
       grind)
    | (have r₁ := eq13 (M.op (M.op X0 X0) (M.op X0 X2)) X0
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq78 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq83 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq90 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq83
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq84
    | exact resolve eq84 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq92
    | exact resolve eq92 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
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
  have eq135 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq153 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq136
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq136
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq136 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq153
  have eq213 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x (M.op (M.op (M.op x X0) (M.op x y)) X1)) X0) := by
    intro X0 X1
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X1)) X0) := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq634 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq680 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4)) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) X2)) y) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq683 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) X2)) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq685 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op x X0) (M.op x y)) X1)) = (M.op (M.op (M.op (M.op x X0) (M.op x y)) (M.op (M.op x (M.op (M.op (M.op x X0) (M.op x y)) X1)) X2)) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq690 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) X3) := by
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
  have eq699 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
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
  have eq705 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) = (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4) (M.op (M.op X0 X1) (M.op X0 X2))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4 X1
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X0 X1 X2 (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4)
       have i₂ := eq52 (M.op (M.op X0 X1) (M.op X0 X2)) X0 X3 X4
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq879 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq77 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq13 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq890 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq879 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq879 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq879 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq879 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq900 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq890 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq890
    | (have j0 := eq890 X0 X1
       grind)
    | exact resolve eq890 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq1097 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) y) := by
    intro X0
    first
    | (have i₁ := eq699 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq699
    | (have j0 := eq699 x y X0
       grind)
    | exact resolve eq699 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1098 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq699
    | (have j0 := eq699 (σ x) (σ y) X0
       grind)
    | exact resolve eq699 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1102 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4) (M.op (M.op X0 X1) (M.op X0 X2))) = (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq699 (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4 X1
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq699
    | exact resolve eq699 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1110 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq699 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq699
    | (have j0 := eq699 x X0 y
       grind)
    | exact resolve eq699 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1111 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq699
    | (have j0 := eq699 (σ x) X0 (σ y)
       grind)
    | exact resolve eq699 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1115 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq699 X0 X1 x
       grind)
    | exact superpose eq699 eq14
    | exact resolve eq14 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1116 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq634 X0 x
       have i₂ := eq699 X0 X0 x
       grind)
    | exact superpose eq699 eq634
    | exact resolve eq634 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq1143 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4) (M.op (M.op X0 X1) (M.op X0 X2))) = (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1102 X0 X1 X2 X3 X4
       have i₂ := eq699 X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)
       grind)
    | exact superpose eq699 eq1102
    | exact resolve eq1102 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1164 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X3)) X4) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X3)) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq1143 X0 X1 x X3 X4
       have i₂ := eq699 X0 X1 x
       grind)
    | exact superpose eq699 eq1143
    | exact resolve eq1143 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq1183 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1115 X0 (M.op X0 X1)
       have i₂ := eq699 X0 X0 X1
       grind)
    | exact superpose eq699 eq1115
    | exact resolve eq1115 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1184 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1115 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq1115 X0 (M.op X0 X0)
       grind)
    | exact superpose eq1115 eq1115
    | exact resolve eq1115 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1188 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1 X1 X0
       have i₂ := eq1115 (M.op X0 X1) X0
       grind)
    | exact superpose eq1115 eq55
    | exact resolve eq55 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1193 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X1
       have i₂ := eq1115 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq1115 eq14
    | exact resolve eq14 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1211 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1188 X0 X1
       have i₂ := eq699 X0 X1 X1
       grind)
    | exact superpose eq699 eq1188
    | exact resolve eq1188 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1218 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq1184 X0
       grind)
    | exact superpose eq1184 eq12
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq1184 X0
       grind)
    | exact resolve eq12 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq1237 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq1218 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218
  have eq1245 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq1237 X0
       have j1 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq1237 x
       have r₂ := eq13 (M.op x x) x
       grind)
    | exact resolve eq1237 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237
  have eq1317 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq1110 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1110
    | (have j0 := eq1110 y
       grind)
    | exact resolve eq1110 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1360 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1317
       have i₂ := eq1097 X0
       grind)
    | exact superpose eq1097 eq1317
    | exact resolve eq1317 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1416 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq26 eq1111
    | (have j0 := eq1111 (σ y)
       grind)
    | exact resolve eq1111 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1459 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1098 eq1416
    | exact resolve eq1416 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1519 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1116 (M.op X0 X0)
       have i₂ := eq1115 X0 (M.op X0 X0)
       grind)
    | exact superpose eq1115 eq1116
    | exact resolve eq1116 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1525 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1519 X0
       have i₂ := eq699 X0 X0 X0
       grind)
    | exact superpose eq699 eq1519
    | exact resolve eq1519 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1519
  have eq1540 : (M.op x x) = (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op x x)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1183 (M.op x x) y
       have i₂ := eq1317
       grind)
    | exact superpose eq1317 eq1183
    | exact resolve eq1183 eq1317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1544 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq213 eq1183
    | exact resolve eq1183 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1546 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1416 eq1183
    | exact resolve eq1183 eq1416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1550 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq222 eq1183
    | exact resolve eq1183 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1579 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq1550
       have i₂ := eq1115 sF4 (M.op sF4 sF4)
       grind)
    | exact superpose eq1115 eq1550
    | exact resolve eq1550 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550
  have eq1583 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1546
       have i₂ := eq1115 sF2 (M.op sF2 sF2)
       grind)
    | exact superpose eq1115 eq1546
    | exact resolve eq1546 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1546
  have eq1585 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1544
       have i₂ := eq1115 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq1115 eq1544
    | exact resolve eq1544 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544
  have eq1589 : (M.op x x) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1540
       have i₂ := eq1115 x (M.op x x)
       grind)
    | exact superpose eq1115 eq1540
    | exact resolve eq1540 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1540
  have eq1621 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1579 eq222
    | exact resolve eq222 eq1579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1631 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1579 eq699
    | exact resolve eq699 eq1579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1642 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq1631 x
       have i₂ := eq699 sF4 sF2 x
       grind)
    | exact superpose eq699 eq1631
    | exact resolve eq1631 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1631
  have eq1647 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq1579 eq1642
    | exact resolve eq1642 eq1579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1642
  have eq1693 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq1585 eq213
    | exact resolve eq213 eq1585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1703 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1585 eq699
    | exact resolve eq699 eq1585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1714 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq1703 x
       have i₂ := eq699 sF0 x x
       grind)
    | exact superpose eq699 eq1703
    | exact resolve eq1703 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1703
  have eq1719 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq1585 eq1714
    | exact resolve eq1714 eq1585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1714
  have eq1807 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq1579 eq1583
    | exact resolve eq1583 eq1579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583
  have eq1850 : (M.op x x) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq1585 eq1589
    | exact resolve eq1589 eq1585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1589
  have eq2421 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1211 (M.op X0 X1) X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq1211
    | exact resolve eq1211 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2422 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq1211 x X0
       have i₂ := eq1110 X0
       grind)
    | exact superpose eq1110 eq1211
    | exact resolve eq1211 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq2423 : x = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | exact superpose eq213 eq1211
    | exact resolve eq1211 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2425 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq222 eq1211
    | exact resolve eq1211 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq2429 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1211 (M.op (M.op X0 X0) X0) (M.op X0 X1)
       have i₂ := eq1183 X0 X1
       grind)
    | exact superpose eq1183 eq1211
    | exact resolve eq1211 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2450 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1115 X0 X1
       have i₂ := eq1211 X0 X1
       grind)
    | (have i₁ := eq1115 X1 X1
       have i₂ := eq1211 X1 X1
       grind)
    | exact superpose eq1211 eq1115
    | exact resolve eq1115 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq2509 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2429 X0 X1
       have i₂ := eq699 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq699 eq2429
    | exact resolve eq2429 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2429
  have eq2516 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2509 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq2509
    | exact resolve eq2509 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2509
  have eq2518 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2516 X0 X1
       have i₂ := eq1193 X0 X0
       grind)
    | exact superpose eq1193 eq2516
    | exact resolve eq2516 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193 eq2516
  have eq2529 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) y) X0) x) = (M.op (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) X0) := by
    intro X0
    first
    | exact superpose eq2423 eq699
    | exact resolve eq699 eq2423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2423
  have eq2532 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) y) X0) x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) y) X0) := by
    intro X0
    first
    | (have i₁ := eq2529 X0
       have i₂ := eq699 sF0 y y
       grind)
    | exact superpose eq699 eq2529
    | exact resolve eq2529 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2529
  have eq2538 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) y) X0) x) := by
    intro X0
    first
    | exact superpose eq213 eq2532
    | exact resolve eq2532 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2532
  have eq2833 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq2518
    | (have j0 := eq2518 (σ x) (σ y)
       grind)
    | exact resolve eq2518 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3999 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) y) := by
    intro X1
    first
    | exact superpose eq1360 eq217
    | (have j0 := eq217 y X1
       grind)
    | exact resolve eq217 eq1360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq4000 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) y) := by
    intro X1
    first
    | exact superpose eq1585 eq3999
    | exact resolve eq3999 eq1585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3999
  have eq4113 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2421 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq2421 X0 X1
       grind)
    | exact superpose eq2421 eq2421
    | exact resolve eq2421 eq2421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4119 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq4000 eq2421
    | exact resolve eq2421 eq4000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4000
  have eq4139 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq2425 eq2421
    | exact resolve eq2421 eq2425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2425
  have eq4176 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2518 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq2421 X0 X1
       grind)
    | exact superpose eq2421 eq2518
    | exact resolve eq2518 eq2421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4177 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4176 X0 X1
       have i₂ := eq699 (M.op X0 X1) X1 X1
       grind)
    | exact superpose eq699 eq4176
    | exact resolve eq4176 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4176
  have eq4199 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq4139
       have i₂ := eq1211 sF2 sF4
       grind)
    | exact superpose eq1211 eq4139
    | exact resolve eq4139 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4139
  have eq4216 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op x (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq1693 eq4119
    | exact resolve eq4119 eq1693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4119
  have eq4220 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4113 X0 X1
       have i₂ := eq1211 X0 (M.op X0 X1)
       grind)
    | exact superpose eq1211 eq4113
    | exact resolve eq4113 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4113
  have eq4234 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4177 X0 X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq4177
    | exact resolve eq4177 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4177
  have eq4248 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq1111 eq4199
    | exact resolve eq4199 eq1111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4199
  have eq4257 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op (M.op x y) x) X0)) := by
    intro X0
    first
    | exact superpose eq1850 eq4216
    | exact resolve eq4216 eq1850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850 eq4216
  have eq4259 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4220 X0 X1
       have i₂ := eq699 X0 X0 X1
       grind)
    | exact superpose eq699 eq4220
    | exact resolve eq4220 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4220
  have eq4349 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op (M.op X0 X1) X1) X0
       have i₂ := eq4234 X0 X1
       grind)
    | exact superpose eq4234 eq13
    | (have j0 := eq13 (M.op (M.op X0 X1) X1) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op X0 X1) X1) X0
       have r₂ := eq4234 X0 X1
       grind)
    | exact resolve eq13 eq4234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4363 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq4349 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4349
  have eq4606 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1459 eq226
    | (have j0 := eq226 (σ y) X1
       grind)
    | exact resolve eq226 eq1459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq4607 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1579 eq4606
    | exact resolve eq4606 eq1579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4606
  have eq4717 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq4607 eq2421
    | exact resolve eq2421 eq4607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4607
  have eq4723 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq1621 eq4717
    | exact resolve eq4717 eq1621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4717
  have eq4731 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq1807 eq4723
    | exact resolve eq4723 eq1807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1807 eq4723
  have eq4893 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x X0) (M.op x y)) (M.op (M.op x (M.op (M.op (M.op x X0) (M.op x y)) X1)) X2)) = (M.op (M.op (M.op x (M.op (M.op (M.op x X0) (M.op x y)) X1)) (M.op x (M.op (M.op (M.op x X0) (M.op x y)) X1))) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq235 eq699
    | exact resolve eq699 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4905 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x X0) (M.op x y)) (M.op (M.op x (M.op (M.op (M.op x X0) (M.op x y)) X1)) X2)) = (M.op (M.op (M.op x (M.op (M.op (M.op x X0) (M.op x y)) X1)) X0) (M.op x (M.op (M.op (M.op x X0) (M.op x y)) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4893 X1 X1 X2
       have i₂ := eq1211 (M.op x (M.op (M.op (M.op x X1) sF0) X1)) X1
       grind)
    | exact superpose eq1211 eq4893
    | exact resolve eq4893 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4893
  have eq4929 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x X0) (M.op x y)) (M.op (M.op x (M.op (M.op (M.op x X0) (M.op x y)) X1)) X2)) = (M.op (M.op (M.op x X0) (M.op x y)) (M.op x (M.op (M.op (M.op x X0) (M.op x y)) X1))) := by
    intro X0 X1 X2
    first
    | exact superpose eq235 eq4905
    | exact resolve eq4905 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq4905
  have eq5109 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op (σ x) X0)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (M.op (σ x) (M.op (σ x) X0)) (M.op (σ x) (σ y))) X1)) := by
    intro X0 X1
    first
    | exact superpose eq240 eq699
    | exact resolve eq699 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq5144 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ x)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) X0)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1111 eq5109
    | exact resolve eq5109 eq1111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111 eq5109
  have eq5169 : ∀ X1 : G, (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (M.op (σ x) (σ x)) (σ x)) X1)) := by
    intro X1
    first
    | (have i₁ := eq5144 x X1
       have i₂ := eq699 sF2 sF2 x
       grind)
    | exact superpose eq699 eq5144
    | exact resolve eq5144 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5144
  have eq5188 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1)) := by
    intro X1
    first
    | exact superpose eq4248 eq5169
    | exact resolve eq5169 eq4248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5169
  have eq5952 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq78 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq78
    | (have j0 := eq78 x
       grind)
    | exact resolve eq78 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq5985 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5952
  have eq5993 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5985
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq5985
    | exact resolve eq5985 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq5985
  have eq6009 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq5993
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq5993 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5993
  have eq6014 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq6009 eq49
    | exact resolve eq49 eq6009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq6765 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq137
    | (have j0 := eq137 (M.op x y)
       grind)
    | exact resolve eq137 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq6786 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq6765
  have eq6789 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq136 eq6786
    | exact resolve eq6786 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq6786
  have eq6812 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq6789
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6789 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6789
  have eq7569 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4259 X0 X2
       have i₂ := eq4259 X0 X1
       grind)
    | (have i₁ := eq4259 X1 X1
       have i₂ := eq4259 X1 X1
       grind)
    | exact superpose eq4259 eq4259
    | exact resolve eq4259 eq4259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7574 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq4248 eq4259
    | exact resolve eq4259 eq4248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4248
  have eq7626 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1183 X0 X2
       have i₂ := eq4259 X0 X1
       grind)
    | (have i₁ := eq1183 X1 X1
       have i₂ := eq4259 X1 X1
       grind)
    | exact superpose eq4259 eq1183
    | exact resolve eq1183 eq4259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9866 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1360 eq682
    | (have j0 := eq682 y X1 X2
       grind)
    | exact resolve eq682 eq1360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq1360
  have eq9867 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) x) X1)) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1585 eq9866
    | exact resolve eq9866 eq1585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9866
  have eq9868 : ∀ X2 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x x) X2)) y) := by
    intro X2
    first
    | exact superpose eq4257 eq9867
    | exact resolve eq9867 eq4257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4257 eq9867
  have eq9995 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x y) (M.op x X0))) y) := by
    intro X0
    first
    | (have i₁ := eq9868 y
       have i₂ := eq1097 X0
       grind)
    | exact superpose eq1097 eq9868
    | exact resolve eq9868 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9868
  have eq10033 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) y) := by
    first
    | (have i₁ := eq9995 x
       have i₂ := eq699 sF0 x (M.op x x)
       grind)
    | exact superpose eq699 eq9995
    | exact resolve eq9995 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9995
  have eq10048 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) y) := by
    first
    | (have i₁ := eq10033
       have i₂ := eq1211 sF0 x
       grind)
    | exact superpose eq1211 eq10033
    | exact resolve eq10033 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10033
  have eq10060 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) x) y) := by
    first
    | exact superpose eq1719 eq10048
    | exact resolve eq10048 eq1719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719 eq10048
  have eq10114 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1459 eq683
    | (have j0 := eq683 (σ y) X1 X2
       grind)
    | exact resolve eq683 eq1459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683 eq1459
  have eq10115 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1579 eq10114
    | exact resolve eq10114 eq1579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10114
  have eq10116 : ∀ X2 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ x)) X2)) (σ y)) := by
    intro X2
    first
    | exact superpose eq4731 eq10115
    | exact resolve eq10115 eq4731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4731 eq10115
  have eq10659 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) (σ y)) := by
    intro X0
    first
    | exact superpose eq1098 eq10116
    | exact resolve eq10116 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10116
  have eq10699 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq10659 x
       have i₂ := eq699 sF4 sF2 (M.op sF2 x)
       grind)
    | exact superpose eq699 eq10659
    | exact resolve eq10659 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10659
  have eq10715 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq10699
       have i₂ := eq1211 sF4 sF2
       grind)
    | exact superpose eq1211 eq10699
    | exact resolve eq10699 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10699
  have eq10728 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1647 eq10715
    | exact resolve eq10715 eq1647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647 eq10715
  have eq10875 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op x X0) x) X1)) = (M.op (M.op (M.op (M.op x X0) x) (M.op (M.op x (M.op (M.op (M.op x X0) x) X1)) X2)) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq2422 eq685
    | exact resolve eq685 eq2422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq12644 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) X0) X0) y) := by
    intro X0
    first
    | (have i₁ := eq10060
       have i₂ := eq7569 sF0 x x
       grind)
    | (have i₁ := eq10060
       have i₂ := eq7569 sF0 x x
       grind)
    | exact superpose eq7569 eq10060
    | exact resolve eq10060 eq7569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10060
  have eq12666 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10728
       have i₂ := eq7569 sF4 sF2 x
       grind)
    | (have i₁ := eq10728
       have i₂ := eq7569 sF4 x sF2
       grind)
    | exact superpose eq7569 eq10728
    | exact resolve eq10728 eq7569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10728
  have eq15516 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op x X0) x) X1)) ≠ X0 ∨ (M.op X0 X0) = (k (M.op (M.op (M.op x X0) x) (M.op (M.op x (M.op (M.op (M.op x X0) x) X1)) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op (M.op x X0) x) (M.op (M.op x (M.op (M.op (M.op x X0) x) X1)) X2)) X0
       have i₂ := eq10875 X0 X1 X2
       grind)
    | exact superpose eq10875 eq13
    | (have j0 := eq13 (M.op (M.op (M.op x X0) x) (M.op (M.op x (M.op (M.op (M.op x X0) x) X1)) X2)) X0
       grind)
    | exact resolve eq13 eq10875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10875
  have eq18488 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X0 X0) X1) X3)) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X3)) X4)) X1) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq680 X0 X1 x X3 X4
       have i₂ := eq699 X0 X1 x
       grind)
    | exact superpose eq699 eq680
    | exact resolve eq680 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq18588 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) y) (M.op (M.op (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) X0) X1)) = (M.op (M.op (M.op (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) X0) (M.op x (M.op (M.op (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) X0) X1))) X0) := by
    intro X0 X1
    first
    | exact superpose eq2538 eq18488
    | exact resolve eq18488 eq2538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18596 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X2))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18488 X0 X1 X2 (M.op X0 x)
       have i₂ := eq699 X0 (M.op (M.op (M.op X0 X0) X1) X2) x
       grind)
    | exact superpose eq699 eq18488
    | exact resolve eq18488 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18488
  have eq18651 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18596 X0 X1 X2
       have i₂ := eq14 (M.op X0 X0) X1 (M.op (M.op (M.op X0 X0) X1) X2)
       grind)
    | exact superpose eq14 eq18596
    | exact resolve eq18596 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18596
  have eq18657 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) y) (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) y) X0) X1)) = (M.op (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) y) X0) (M.op x (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) y) X0) X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18588 X0 X1
       have i₂ := eq699 sF0 y y
       grind)
    | exact superpose eq699 eq18588
    | exact resolve eq18588 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18588
  have eq18723 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) y) (M.op (M.op x X0) X1)) = (M.op (M.op (M.op x X0) (M.op x (M.op (M.op x X0) X1))) X0) := by
    intro X0 X1
    first
    | exact superpose eq213 eq18657
    | exact resolve eq18657 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq18657
  have eq18772 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) y) (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18723 X0 X1
       have i₂ := eq14 x X0 (M.op (M.op x X0) X1)
       grind)
    | exact superpose eq14 eq18723
    | exact resolve eq18723 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18723
  have eq18955 : ∀ X0 X1 : G, (M.op x x) = (M.op x (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq18772 eq2538
    | exact resolve eq2538 eq18772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19029 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) X3) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq690 X0 X1 x X3 X4
       have i₂ := eq699 X0 X1 x
       grind)
    | exact superpose eq699 eq690
    | exact resolve eq690 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq19094 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X2)) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X2)) X3)) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X2)) X0) X4)) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19029 X0 (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X2)) X3) X1 X4
       have i₂ := eq52 (M.op X0 X0) X1 X2 X3
       grind)
    | exact superpose eq52 eq19029
    | exact resolve eq19029 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq19134 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) (M.op (M.op X0 X0) (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19029 X0 (M.op X0 X1) X2 X2
       have i₂ := eq55 X0 X0 X1 X2
       grind)
    | exact superpose eq55 eq19029
    | exact resolve eq19029 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq19029
  have eq19240 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19134 X0 X1 X2
       have i₂ := eq699 (M.op X0 X0) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq699 eq19134
    | exact resolve eq19134 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19134
  have eq19276 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) X3)) (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) X0) X4)) X1) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq19094 X0 X1 x X3 X4
       have i₂ := eq699 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq699 eq19094
    | exact resolve eq19094 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19094
  have eq19349 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19240 X0 X1 X2
       have i₂ := eq699 X0 X0 X0
       grind)
    | exact superpose eq699 eq19240
    | exact resolve eq19240 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19240
  have eq19381 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X0 X0) X0) X1) X3)) (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) X4)) X1) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq19276 x X1 X3 X4
       have i₂ := eq699 x x x
       grind)
    | exact superpose eq699 eq19276
    | exact resolve eq19276 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19276
  have eq19420 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19349 X0 X1 X2
       have i₂ := eq7626 X0 X0 X1
       grind)
    | exact superpose eq7626 eq19349
    | exact resolve eq19349 eq7626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19349
  have eq19460 : ∀ X0 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X0) X0) X2) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq19420 X0 x X2
       have i₂ := eq699 X0 X0 x
       grind)
    | exact superpose eq699 eq19420
    | exact resolve eq19420 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19420
  have eq19739 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X0 X0) X1) X3)) = (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X3)) X4) (M.op (M.op X0 X0) X1)) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq705 X0 X1 x X3 X4
       have i₂ := eq699 X0 X1 x
       grind)
    | exact superpose eq699 eq705
    | exact resolve eq705 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq25122 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq772 X0 X1 X2 X3 x
       have i₂ := eq2518 (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) x
       grind)
    | exact superpose eq2518 eq772
    | exact resolve eq772 eq2518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq25123 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0)) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25122 X0 X1 X2 X3
       have i₂ := eq699 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)
       grind)
    | exact superpose eq699 eq25122
    | exact resolve eq25122 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25122
  have eq25124 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op (M.op X0 X0) X1) X0)) (M.op (M.op (M.op X0 X0) X1) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq25123 X0 X1 x X3
       have i₂ := eq699 X0 X1 x
       grind)
    | exact superpose eq699 eq25123
    | exact resolve eq25123 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25123
  have eq25125 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op X0 X0) X1) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq25124 X0 X1 X3
       have i₂ := eq699 (M.op (M.op X0 X0) X1) X0 X0
       grind)
    | exact superpose eq699 eq25124
    | exact resolve eq25124 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25124
  have eq25126 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op X0 X0) X1)) (M.op (M.op (M.op X0 X0) X1) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq25125 X0 X1 X3
       have i₂ := eq1211 (M.op (M.op X0 X0) X1) X0
       grind)
    | exact superpose eq1211 eq25125
    | exact resolve eq25125 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25125
  have eq25237 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 X0) X1))) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25126 (M.op X0 (M.op (M.op (M.op X0 X0) X1) x)) (M.op (M.op X0 X0) X1) (M.op X0 (M.op (M.op (M.op X0 X0) X1) x))
       have i₂ := eq19739 X0 X1 x (M.op X0 (M.op (M.op (M.op X0 X0) X1) x))
       grind)
    | exact superpose eq19739 eq25126
    | exact resolve eq25126 eq19739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19739 eq25126
  have eq25325 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25237 X0 X1 X2
       have i₂ := eq1211 (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 X0) X1))
       grind)
    | exact superpose eq1211 eq25237
    | exact resolve eq25237 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25237
  have eq25448 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25325 X0 X1 X2
       have i₂ := eq2518 (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq2518 eq25325
    | exact resolve eq25325 eq2518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25325
  have eq25554 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25448 X0 X1 X2
       have i₂ := eq699 (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))
       grind)
    | exact superpose eq699 eq25448
    | exact resolve eq25448 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25448
  have eq25616 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X2)) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25554 X0 X1 X2
       have i₂ := eq699 X0 (M.op (M.op (M.op X0 X0) X1) X2) (M.op (M.op (M.op X0 X0) X1) X2)
       grind)
    | exact superpose eq699 eq25554
    | exact resolve eq25554 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25554
  have eq25650 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op (M.op X0 X0) X1) X2)) = (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25616 X0 X1 X2
       have i₂ := eq699 (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X2) X1
       grind)
    | exact superpose eq699 eq25616
    | exact resolve eq25616 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25616
  have eq25669 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X1) X2)) = (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25650 X0 X1 X2
       have i₂ := eq699 X0 X0 X0
       grind)
    | exact superpose eq699 eq25650
    | exact resolve eq25650 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25650
  have eq34916 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq6009 eq90
    | exact resolve eq90 eq6009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq6009
  have eq34921 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq95 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34930 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq34921
    | exact resolve eq34921 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34921
  have eq34935 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq34930
       have r₂ := eq27
       grind)
    | exact resolve eq34930 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34930
  have eq34937 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq34935
    | exact resolve eq34935 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34935
  have eq34939 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq34937 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq34937
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq34937
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq34937
       grind)
    | exact resolve eq12 eq34937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34953 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq34937 eq2450
    | exact resolve eq2450 eq34937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34937
  have eq34964 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq34939
  have eq34966 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq34953
       have i₂ := eq1211 sF2 sF3
       grind)
    | exact superpose eq1211 eq34953
    | exact resolve eq34953 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34953
  have eq34972 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq34964
    | exact resolve eq34964 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34964
  have eq34973 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq34972
  have eq34975 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1416 eq34966
    | exact resolve eq34966 eq1416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1416 eq34966
  have eq34976 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1579 eq34975
    | exact resolve eq34975 eq1579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1579 eq34975
  have eq34979 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq34973 eq95
    | exact resolve eq95 eq34973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34973
  have eq34992 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq34979
  have eq35143 : y = (M.op (M.op x x) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4234 y x
       have i₂ := eq34992
       grind)
    | exact superpose eq34992 eq4234
    | exact resolve eq4234 eq34992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34992
  have eq35153 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35143
       have i₂ := eq1317
       grind)
    | exact superpose eq1317 eq35143
    | exact resolve eq35143 eq1317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35143
  have eq35162 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1585 eq35153
    | exact resolve eq35153 eq1585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35153
  have eq35465 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35162 eq1693
    | exact resolve eq1693 eq35162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693
  have eq35970 : x = (k (M.op x y) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4363 y y
       have i₂ := eq35465
       grind)
    | exact superpose eq35465 eq4363
    | exact resolve eq4363 eq35465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4363 eq35465
  have eq35982 : x = (k (M.op x y) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35970
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35970
    | exact resolve eq35970 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35970
  have eq36724 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35982 eq135
    | exact resolve eq135 eq35982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq35982
  have eq36754 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36724
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36724
    | exact resolve eq36724 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36724
  have eq37185 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq34976 eq1621
    | exact resolve eq1621 eq34976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1621 eq34976
  have eq37354 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1585 eq160
    | exact resolve eq160 eq1585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq37355 : (σ (M.op (M.op x y) x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq6812 eq37354
    | exact resolve eq37354 eq6812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6812 eq37354
  have eq37356 : (σ (M.op (M.op x y) x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1585 eq37355
    | exact resolve eq37355 eq1585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37355
  have eq46573 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35162 eq37356
    | exact resolve eq37356 eq35162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35162 eq37356
  have eq46635 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq46573
  have eq46642 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46635
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq46635
    | exact resolve eq46635 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46635
  have eq46657 : (M.op (σ y) (σ (M.op x y))) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46642 eq1525
    | exact resolve eq1525 eq46642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1525
  have eq46693 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ (M.op x y))) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46642 eq1183
    | exact resolve eq1183 eq46642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183 eq46642
  have eq47969 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46657 eq36754
    | exact resolve eq36754 eq46657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36754 eq46657
  have eq47982 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq47969
  have eq49236 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq47982 eq46693
    | exact resolve eq46693 eq47982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46693 eq47982
  have eq49263 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq49236
  have eq49274 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq49263
    | exact resolve eq49263 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49263
  have eq49283 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq49274
       have r₂ := eq27
       grind)
    | exact resolve eq49274 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49274
  have eq49288 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq49283 eq66
    | (have r₁ := eq66
       have r₂ := eq49283
       grind)
    | exact resolve eq66 eq49283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq49316 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq49283 eq2833
    | exact resolve eq2833 eq49283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49349 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ y) X0) X0) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq49283 eq12666
    | exact resolve eq12666 eq49283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12666 eq49283
  have eq49362 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq49288
  have eq49363 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq49349 x
       have i₂ := eq4234 sF3 x
       grind)
    | exact superpose eq4234 eq49349
    | exact resolve eq49349 eq4234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49349
  have eq49367 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq49316
    | exact resolve eq49316 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49316
  have eq49392 : (τ (σ y)) = (k x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq49363 eq6014
    | exact resolve eq6014 eq49363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49408 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq49363 eq1098
    | exact resolve eq1098 eq49363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098 eq49363
  have eq49509 : y = (k x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq49392
    | exact resolve eq49392 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq49392
  have eq49747 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq49367 eq6014
    | exact resolve eq6014 eq49367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6014 eq49367
  have eq50399 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq49509
       grind)
    | exact superpose eq49509 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq49509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50415 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq50399
  have eq51850 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq49362 eq95
    | exact resolve eq95 eq49362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq49362
  have eq51867 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq51850
  have eq348754 : y = (M.op x y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2518 x x
       have i₂ := eq50415
       grind)
    | exact superpose eq50415 eq2518
    | exact resolve eq2518 eq50415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50415
  have eq348784 : y = (M.op x y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq348754
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq348754
    | exact resolve eq348754 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348754
  have eq348785 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq348784
  have eq348869 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1097 x
       have i₂ := eq348785
       grind)
    | exact superpose eq348785 eq1097
    | exact resolve eq1097 eq348785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097
  have eq348916 : x = (k x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1245 x
       have i₂ := eq348785
       grind)
    | exact superpose eq348785 eq1245
    | exact resolve eq1245 eq348785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1245 eq348785
  have eq349058 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq348869
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq348869
    | exact resolve eq348869 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348869
  have eq349535 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq49509
       have i₂ := eq348916
       grind)
    | exact superpose eq348916 eq49509
    | exact resolve eq49509 eq348916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49509
  have eq349536 : x = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq49747
       have i₂ := eq348916
       grind)
    | exact superpose eq348916 eq49747
    | exact resolve eq49747 eq348916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49747 eq348916
  have eq349596 : x = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq349536
  have eq349597 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq349535
  have eq349709 : x = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq349597 eq28
    | exact resolve eq28 eq349597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349597
  have eq350291 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq349709
    | exact resolve eq349709 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349709
  have eq350299 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq350291 eq20
    | exact resolve eq20 eq350291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350522 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op y X0) X0) y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq350291 eq12644
    | exact resolve eq12644 eq350291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12644 eq350291
  have eq350571 : y = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq350522 x
       have i₂ := eq4234 y x
       grind)
    | exact superpose eq4234 eq350522
    | exact resolve eq350522 eq4234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350522
  have eq350712 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq350299
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq350299
    | exact resolve eq350299 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350299
  have eq351641 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq349596 eq15
    | exact resolve eq15 eq349596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349596
  have eq352006 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq351641
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq351641
    | exact resolve eq351641 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351641
  have eq352117 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq352006 eq49408
    | exact resolve eq49408 eq352006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49408 eq352006
  have eq352852 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq352117
  have eq353028 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq352852
    | exact resolve eq352852 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352852
  have eq358153 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq34916
       have i₂ := eq350571
       grind)
    | exact superpose eq350571 eq34916
    | exact resolve eq34916 eq350571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34916 eq350571
  have eq358304 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq358153
  have eq358336 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq358304
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq358304
    | exact resolve eq358304 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358304
  have eq358844 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq353028 eq51867
    | exact resolve eq51867 eq353028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51867 eq353028
  have eq359149 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq358844
  have eq359242 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq359149
       have r₂ := eq27
       grind)
    | exact resolve eq359149 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359149
  have eq377854 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq358336 eq2518
    | exact resolve eq2518 eq358336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2518 eq358336
  have eq377911 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq377854
    | exact resolve eq377854 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377854
  have eq377950 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq377911 eq27
    | exact resolve eq27 eq377911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377911
  have eq378541 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq377950
       have r₂ := eq350712
       grind)
    | exact resolve eq377950 eq350712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350712 eq377950
  have eq419157 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X3)) X4) = (M.op (M.op (M.op X0 X0) X4) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq1164 X0 X1 X3 X4
       have i₂ := eq18651 X0 X1 X3
       grind)
    | exact superpose eq18651 eq1164
    | exact resolve eq1164 eq18651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164 eq18651
  have eq419158 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X3)) X4) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq419157 X0 X1 X3 X4
       have i₂ := eq699 (M.op X0 X0) X4 X1
       grind)
    | exact superpose eq699 eq419157
    | exact resolve eq419157 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419157
  have eq419159 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X3)) X4) = (M.op (M.op (M.op X0 X0) X0) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq419158 X0 X1 X3 X4
       have i₂ := eq699 X0 X0 X0
       grind)
    | exact superpose eq699 eq419158
    | exact resolve eq419158 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419158
  have eq497480 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x X0) x) (M.op x (M.op (M.op (M.op x X0) x) X1))) = (M.op (M.op (M.op x X0) x) (M.op (M.op x (M.op (M.op (M.op x X0) x) X1)) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq2422 eq4929
    | exact resolve eq4929 eq2422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2422 eq4929
  have eq550315 : y = (M.op (M.op x x) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4234 y x
       have i₂ := eq359242
       grind)
    | exact superpose eq359242 eq4234
    | exact resolve eq4234 eq359242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4234 eq359242
  have eq550356 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq550315
       have i₂ := eq1317
       grind)
    | exact superpose eq1317 eq550315
    | exact resolve eq550315 eq1317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1317 eq550315
  have eq550373 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1585 eq550356
    | exact resolve eq550356 eq1585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1585 eq550356
  have eq550378 : ∀ X0 X1 : G, (M.op x (M.op (M.op (M.op x X0) x) X1)) ≠ X0 ∨ (M.op X0 X0) = (k (M.op (M.op (M.op x X0) x) (M.op x (M.op (M.op (M.op x X0) x) X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15516 X0 X1 x
       have i₂ := eq497480 X0 X1 x
       grind)
    | exact superpose eq497480 eq15516
    | (have j0 := eq15516 X0 X1 x
       grind)
    | exact resolve eq15516 eq497480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15516 eq497480
  have eq571700 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq550373 eq349058
    | exact resolve eq349058 eq550373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349058 eq550373
  have eq571783 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq571700
  have eq571872 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq571783 eq28
    | exact resolve eq28 eq571783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq571783
  have eq572632 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq571872
    | exact resolve eq571872 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq571872
  have eq572964 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq572632
  have eq572970 : x = (M.op x y) := by
    first
    | (have r₁ := eq572964
       have r₂ := eq378541
       grind)
    | exact resolve eq572964 eq378541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378541 eq572964
  have eq573170 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq572970 eq20
    | exact resolve eq20 eq572970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq573281 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op x y) X0) x) := by
    intro X0
    first
    | exact superpose eq572970 eq2538
    | exact resolve eq2538 eq572970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2538
  have eq573410 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq572970 eq18772
    | exact resolve eq18772 eq572970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18772
  have eq573536 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq573410 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq573410
    | (have j0 := eq573410 X0 X1
       grind)
    | exact resolve eq573410 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573410
  have eq573612 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op x y) X0) x) := by
    intro X0
    first
    | (have i₁ := eq573281 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq573281
    | (have j0 := eq573281 X0
       grind)
    | exact resolve eq573281 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573281
  have eq573698 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq573170
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq573170
    | exact resolve eq573170 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573170
  have eq573713 : ∀ X0 X1 : G, x = (M.op x (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq572970 eq573536
    | exact resolve eq573536 eq572970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573536
  have eq573735 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | exact superpose eq572970 eq573612
    | exact resolve eq573612 eq572970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573612
  have eq573766 : x = (M.op x x) := by
    first
    | (have i₁ := eq573713 x x
       have i₂ := eq18955 x x
       grind)
    | exact superpose eq18955 eq573713
    | exact resolve eq573713 eq18955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18955 eq573713
  have eq573849 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq573698 eq26
    | exact resolve eq26 eq573698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq578114 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X1) X2)) = (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25669 X0 X1 X2
       have i₂ := eq419159 X0 X1 X2 (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))
       grind)
    | exact superpose eq419159 eq25669
    | exact resolve eq25669 eq419159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25669 eq419159
  have eq578115 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq578114 X0 X1 X2
       have i₂ := eq7626 X0 X0 (M.op (M.op (M.op X0 X0) X1) X2)
       grind)
    | exact superpose eq7626 eq578114
    | exact resolve eq578114 eq7626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7626 eq578114
  have eq578594 : x ≠ (M.op x x) ∨ (M.op x x) = (k (M.op (M.op (M.op x x) x) (M.op x x)) x) := by
    first
    | (have i₁ := eq550378 x (M.op (M.op (M.op x x) x) x)
       have i₂ := eq578115 x x x
       grind)
    | exact superpose eq578115 eq550378
    | exact resolve eq550378 eq578115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550378 eq578115
  have eq578771 : (M.op x x) = (k (M.op (M.op (M.op x x) x) (M.op x x)) x) := by
    first
    | (have r₁ := eq578594
       have r₂ := eq573766
       grind)
    | exact resolve eq578594 eq573766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578594
  have eq578963 : (k x x) = (M.op x x) := by
    first
    | (have i₁ := eq578771
       have i₂ := eq2421 x x
       grind)
    | exact superpose eq2421 eq578771
    | exact resolve eq578771 eq2421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2421 eq578771
  have eq579107 : x = (k x x) := by
    first
    | (have i₁ := eq578963
       have i₂ := eq573766
       grind)
    | exact superpose eq573766 eq578963
    | exact resolve eq578963 eq573766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573766 eq578963
  have eq579489 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq900 x x
       have i₂ := eq579107
       grind)
    | exact superpose eq579107 eq900
    | (have j0 := eq900 x x
       grind)
    | exact resolve eq900 eq579107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900 eq579107
  have eq579508 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq579489
  have eq579509 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq579508
  have eq579534 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq579509
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq579509
    | exact resolve eq579509 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579509
  have eq579585 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq573698 eq579534
    | exact resolve eq579534 eq573698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579534
  have eq580921 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq573849 eq1211
    | exact resolve eq1211 eq573849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq580927 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq573849 eq4259
    | exact resolve eq4259 eq573849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4259
  have eq580964 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq579585 eq580927
    | exact resolve eq580927 eq579585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580927
  have eq580968 : (M.op (σ (M.op x y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq579585 eq580921
    | exact resolve eq580921 eq579585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580921
  have eq581006 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq579585 eq580964
    | exact resolve eq580964 eq579585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580964
  have eq581007 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq573849 eq580968
    | exact resolve eq580968 eq573849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580968
  have eq582963 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq581006 eq7569
    | exact resolve eq7569 eq581006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7569
  have eq582992 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq573849 eq582963
    | exact resolve eq582963 eq573849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582963
  have eq646540 : ∀ X0 X1 X3 X4 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X0 X0) X0) X1) X3)) (M.op (M.op X0 X1) X4)) X1) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq19381 X0 x X3 X4
       have i₂ := eq19460 X0 x
       grind)
    | exact superpose eq19460 eq19381
    | exact resolve eq19381 eq19460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19381 eq19460
  have eq648959 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0)) (M.op (σ x) X1)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq37185 eq646540
    | exact resolve eq646540 eq37185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37185 eq646540
  have eq650272 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq648959 X0 x
       have i₂ := eq699 sF2 (M.op (M.op (M.op sF2 sF3) sF3) X0) x
       grind)
    | exact superpose eq699 eq648959
    | exact resolve eq648959 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699 eq648959
  have eq651445 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq7574 eq650272
    | (have j0 := eq650272 X0
       grind)
    | exact resolve eq650272 eq7574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7574 eq650272
  have eq652525 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq5188 eq651445
    | exact resolve eq651445 eq5188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5188 eq651445
  have eq653523 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq582992 eq652525
    | exact resolve eq652525 eq582992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582992 eq652525
  have eq654383 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq573698 eq653523
    | exact resolve eq653523 eq573698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653523
  have eq655110 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq654383
       have r₂ := eq27
       grind)
    | exact resolve eq654383 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654383
  have eq655737 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq572970 eq655110
    | exact resolve eq655110 eq572970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655110
  have eq662314 : y = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2450 y x
       have i₂ := eq655737
       grind)
    | exact superpose eq655737 eq2450
    | exact resolve eq2450 eq655737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2450 eq655737
  have eq662370 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq662314
       have i₂ := eq573735 y
       grind)
    | exact superpose eq573735 eq662314
    | exact resolve eq662314 eq573735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573735 eq662314
  have eq662392 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq662370
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq662370
    | exact resolve eq662370 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq662370
  have eq662401 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq572970 eq662392
    | exact resolve eq662392 eq572970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572970 eq662392
  have eq662402 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq662401
  have eq662442 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq662402 eq2833
    | exact resolve eq2833 eq662402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2833 eq662402
  have eq663075 : (M.op (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq573698 eq662442
    | exact resolve eq662442 eq573698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662442
  have eq663171 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq579585 eq663075
    | exact resolve eq663075 eq579585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579585 eq663075
  have eq663208 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq573849 eq663171
    | exact resolve eq663171 eq573849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573849 eq663171
  have eq663222 : x = y := by
    first
    | (have r₁ := eq663208
       have r₂ := eq27
       grind)
    | exact resolve eq663208 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663208
  have eq663226 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq663222
       grind)
    | exact superpose eq663222 eq24
    | exact resolve eq24 eq663222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq663222
  have eq663777 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq663226
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq663226
    | exact resolve eq663226 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq663226
  have eq663952 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq573698 eq663777
    | exact resolve eq663777 eq573698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573698 eq663777
  have eq673969 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq663952 eq581006
    | exact resolve eq581006 eq663952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581006 eq663952
  have eq674000 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq581007 eq673969
    | exact resolve eq673969 eq581007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581007 eq673969
  have eq674127 : False := by grind
  exact eq674127

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_x_pxx_pxy_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X0 := by
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
  clear eq35
  have eq50 : y ≠ (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1) := by
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
  have eq59 : ∀ X0 : G, x = (M.op (M.op (M.op x X0) (M.op x y)) X0) := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3) := by
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
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq73 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq73
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq74
    | exact resolve eq74 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq81
    | exact resolve eq81 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq83
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq83
    | exact resolve eq83 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq213 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq56 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq56
    | (have j0 := eq56 y
       grind)
    | exact resolve eq56 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq57
    | (have j0 := eq57 (σ y)
       grind)
    | exact resolve eq57 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) x) X1) := by
    intro X0 X1
    first
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq623 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) X2)) y) := by
    intro X0 X1 X2
    first
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq624 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) X2)) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq57 eq58
    | exact resolve eq58 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq640 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 X1 X2 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq815 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq69 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq69 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq69 X0 X1
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq826 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq815 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq828 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq826 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq826 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq826 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq826 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq838 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq828 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq828
    | (have j0 := eq828 X0 X1
       grind)
    | exact resolve eq828 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq1000 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) y) := by
    intro X0
    first
    | (have i₁ := eq640 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq640
    | (have j0 := eq640 x y X0
       grind)
    | exact resolve eq640 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1001 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq640
    | (have j0 := eq640 (σ x) (σ y) X0
       grind)
    | exact resolve eq640 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1013 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq640 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq640
    | (have j0 := eq640 x X0 y
       grind)
    | exact resolve eq640 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1014 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq640
    | (have j0 := eq640 (σ x) X0 (σ y)
       grind)
    | exact resolve eq640 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1018 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq640 X0 X1 x
       grind)
    | exact superpose eq640 eq14
    | exact resolve eq14 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1080 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1018 X0 (M.op X0 X1)
       have i₂ := eq640 X0 X0 X1
       grind)
    | exact superpose eq640 eq1018
    | exact resolve eq1018 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1085 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1 X1 X0
       have i₂ := eq1018 (M.op X0 X1) X0
       grind)
    | exact superpose eq1018 eq61
    | exact resolve eq61 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq1090 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X1
       have i₂ := eq1018 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq1018 eq14
    | exact resolve eq14 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1106 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1085 X0 X1
       have i₂ := eq640 X0 X1 X1
       grind)
    | exact superpose eq640 eq1085
    | exact resolve eq1085 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq1394 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq1013 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1013
    | (have j0 := eq1013 y
       grind)
    | exact resolve eq1013 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1430 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1394
       have i₂ := eq1000 X0
       grind)
    | exact superpose eq1000 eq1394
    | exact resolve eq1394 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1580 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq26 eq1014
    | (have j0 := eq1014 (σ y)
       grind)
    | exact resolve eq1014 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1616 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1001 eq1580
    | exact resolve eq1580 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1735 : (M.op x x) = (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op x x)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1080 (M.op x x) y
       have i₂ := eq1394
       grind)
    | exact superpose eq1394 eq1080
    | exact resolve eq1080 eq1394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394
  have eq1739 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq213 eq1080
    | exact resolve eq1080 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1741 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1580 eq1080
    | exact resolve eq1080 eq1580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1580
  have eq1745 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq222 eq1080
    | exact resolve eq1080 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1772 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq1745
       have i₂ := eq1018 sF4 (M.op sF4 sF4)
       grind)
    | exact superpose eq1018 eq1745
    | exact resolve eq1745 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1745
  have eq1776 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1741
       have i₂ := eq1018 sF2 (M.op sF2 sF2)
       grind)
    | exact superpose eq1018 eq1741
    | exact resolve eq1741 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1741
  have eq1778 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1739
       have i₂ := eq1018 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq1018 eq1739
    | exact resolve eq1739 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1739
  have eq1782 : (M.op x x) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1735
       have i₂ := eq1018 x (M.op x x)
       grind)
    | exact superpose eq1018 eq1735
    | exact resolve eq1735 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018 eq1735
  have eq1869 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1772 eq222
    | exact resolve eq222 eq1772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1878 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1772 eq640
    | exact resolve eq640 eq1772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1886 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq1878 x
       have i₂ := eq640 sF4 sF2 x
       grind)
    | exact superpose eq640 eq1878
    | exact resolve eq1878 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878
  have eq1889 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq1772 eq1886
    | exact resolve eq1886 eq1772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886
  have eq1892 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq1778 eq213
    | exact resolve eq213 eq1778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1901 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1778 eq640
    | exact resolve eq640 eq1778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1909 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq1901 x
       have i₂ := eq640 sF0 x x
       grind)
    | exact superpose eq640 eq1901
    | exact resolve eq1901 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1901
  have eq1912 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq1778 eq1909
    | exact resolve eq1909 eq1778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1909
  have eq2059 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq1772 eq1776
    | exact resolve eq1776 eq1772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776
  have eq2109 : (M.op x x) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq1778 eq1782
    | exact resolve eq1782 eq1778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1782
  have eq2748 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1106 (M.op X0 X1) X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq1106
    | exact resolve eq1106 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2749 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq1106 x X0
       have i₂ := eq1013 X0
       grind)
    | exact superpose eq1013 eq1106
    | exact resolve eq1106 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2750 : x = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | exact superpose eq213 eq1106
    | exact resolve eq1106 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2752 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq222 eq1106
    | exact resolve eq1106 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2756 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1106 (M.op (M.op X0 X0) X0) (M.op X0 X1)
       have i₂ := eq1080 X0 X1
       grind)
    | exact superpose eq1080 eq1106
    | exact resolve eq1106 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2832 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2756 X0 X1
       have i₂ := eq1090 X0 X0
       grind)
    | exact superpose eq1090 eq2756
    | exact resolve eq2756 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090 eq2756
  have eq2838 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2832 X0 X1
       have i₂ := eq640 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq640 eq2832
    | exact resolve eq2832 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2832
  have eq2839 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2838 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq2838
    | exact resolve eq2838 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2838
  have eq2849 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) y) X0) x) = (M.op (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) X0) := by
    intro X0
    first
    | exact superpose eq2750 eq640
    | exact resolve eq640 eq2750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2852 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) y) X0) x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) y) X0) := by
    intro X0
    first
    | (have i₁ := eq2849 X0
       have i₂ := eq640 sF0 y y
       grind)
    | exact superpose eq640 eq2849
    | exact resolve eq2849 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2849
  have eq2857 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) y) X0) x) := by
    intro X0
    first
    | exact superpose eq213 eq2852
    | exact resolve eq2852 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2852
  have eq3292 : (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = (M.op (M.op (M.op x y) y) x) := by
    first
    | exact superpose eq2750 eq2839
    | exact resolve eq2839 eq2750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3301 : (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq2752 eq2839
    | exact resolve eq2839 eq2752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3305 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq2839 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2839
    | (have j0 := eq2839 x y
       grind)
    | exact resolve eq2839 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3311 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq2839
    | (have j0 := eq2839 (σ x) (σ y)
       grind)
    | exact resolve eq2839 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2839
  have eq3366 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq3301
       have i₂ := eq640 sF4 sF3 sF3
       grind)
    | exact superpose eq640 eq3301
    | exact resolve eq3301 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3301
  have eq3375 : (M.op (M.op (M.op x y) (M.op x y)) y) = (M.op (M.op (M.op x y) y) x) := by
    first
    | (have i₁ := eq3292
       have i₂ := eq640 sF0 y y
       grind)
    | exact superpose eq640 eq3292
    | exact resolve eq3292 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3292
  have eq3401 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq222 eq3366
    | exact resolve eq3366 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq3366
  have eq3409 : x = (M.op (M.op (M.op x y) y) x) := by
    first
    | exact superpose eq213 eq3375
    | exact resolve eq3375 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq3375
  have eq3618 : (σ x) ≠ (σ x) ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq3401 eq13
    | (have j0 := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)
       grind)
    | (have r₁ := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)
       have r₂ := eq3401
       grind)
    | exact resolve eq13 eq3401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3401
  have eq3630 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by grind
  clear eq3618
  have eq3644 : x ≠ x ∨ (M.op (M.op x y) y) = (k (M.op (M.op x y) y) x) := by
    first
    | exact superpose eq3409 eq13
    | (have j0 := eq13 (M.op (M.op x y) y) x
       grind)
    | (have r₁ := eq13 (M.op (M.op x y) y) x
       have r₂ := eq3409
       grind)
    | exact resolve eq13 eq3409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3409
  have eq3656 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) x) := by grind
  clear eq3644
  have eq3815 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2748 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq2748 X0 X1
       grind)
    | exact superpose eq2748 eq2748
    | exact resolve eq2748 eq2748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3828 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq2750 eq2748
    | exact resolve eq2748 eq2750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2750
  have eq3838 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq2752 eq2748
    | exact resolve eq2748 eq2752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2752
  have eq3893 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq3838
       have i₂ := eq1106 sF2 sF4
       grind)
    | exact superpose eq1106 eq3838
    | exact resolve eq3838 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3838
  have eq3901 : (M.op (M.op x y) y) = (M.op (M.op x x) (M.op x y)) := by
    first
    | (have i₁ := eq3828
       have i₂ := eq1106 x sF0
       grind)
    | exact superpose eq1106 eq3828
    | exact resolve eq3828 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3828
  have eq3912 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3815 X0 X1
       have i₂ := eq1106 X0 (M.op X0 X1)
       grind)
    | exact superpose eq1106 eq3815
    | exact resolve eq3815 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3815
  have eq3937 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq1014 eq3893
    | exact resolve eq3893 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014 eq3893
  have eq3941 : (M.op (M.op x y) y) = (M.op (M.op x x) x) := by
    first
    | exact superpose eq1013 eq3901
    | exact resolve eq3901 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013 eq3901
  have eq3946 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3912 X0 X1
       have i₂ := eq640 X0 X0 X1
       grind)
    | exact superpose eq640 eq3912
    | exact resolve eq3912 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3912
  have eq4242 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) y) := by
    intro X1
    first
    | exact superpose eq1430 eq216
    | (have j0 := eq216 y X1
       grind)
    | exact resolve eq216 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq4243 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) y) := by
    intro X1
    first
    | exact superpose eq1778 eq4242
    | exact resolve eq4242 eq1778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4242
  have eq4344 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq4243 eq2748
    | exact resolve eq2748 eq4243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4243
  have eq4350 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op x (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq1892 eq4344
    | exact resolve eq4344 eq1892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1892 eq4344
  have eq4357 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op (M.op x y) x) X0)) := by
    intro X0
    first
    | exact superpose eq2109 eq4350
    | exact resolve eq4350 eq2109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2109 eq4350
  have eq4503 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1616 eq225
    | (have j0 := eq225 (σ y) X1
       grind)
    | exact resolve eq225 eq1616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq4504 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1772 eq4503
    | exact resolve eq4503 eq1772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4503
  have eq4603 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq4504 eq2748
    | exact resolve eq2748 eq4504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4504
  have eq4609 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq1869 eq4603
    | exact resolve eq4603 eq1869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869 eq4603
  have eq4616 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq2059 eq4609
    | exact resolve eq4609 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059 eq4609
  have eq4797 : ∀ X0 X1 : G, (M.op (M.op x X0) x) = (M.op (M.op (M.op (M.op (M.op x X0) x) X1) x) X1) := by
    intro X0 X1
    first
    | exact superpose eq2749 eq233
    | exact resolve eq233 eq2749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq2749
  have eq5877 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op (M.op (M.op x y) y) X0) x) X0) := by
    intro X0
    first
    | (have i₁ := eq4797 x x
       have i₂ := eq3941
       grind)
    | exact superpose eq3941 eq4797
    | exact resolve eq4797 eq3941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3941 eq4797
  have eq5925 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | exact superpose eq2857 eq5877
    | exact resolve eq5877 eq2857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2857 eq5877
  have eq6028 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3946 X0 X2
       have i₂ := eq3946 X0 X1
       grind)
    | (have i₁ := eq3946 X1 X1
       have i₂ := eq3946 X1 X1
       grind)
    | exact superpose eq3946 eq3946
    | exact resolve eq3946 eq3946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6033 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq3937 eq3946
    | exact resolve eq3946 eq3937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3937
  have eq6082 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1080 X0 X2
       have i₂ := eq3946 X0 X1
       grind)
    | (have i₁ := eq1080 X1 X1
       have i₂ := eq3946 X1 X1
       grind)
    | exact superpose eq3946 eq1080
    | exact resolve eq1080 eq3946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3946
  have eq11824 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1430 eq623
    | (have j0 := eq623 y X1 X2
       grind)
    | exact resolve eq623 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623 eq1430
  have eq11825 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) x) X1)) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1778 eq11824
    | exact resolve eq11824 eq1778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1778 eq11824
  have eq11826 : ∀ X2 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x x) X2)) y) := by
    intro X2
    first
    | exact superpose eq4357 eq11825
    | exact resolve eq11825 eq4357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4357 eq11825
  have eq11906 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x y) (M.op x X0))) y) := by
    intro X0
    first
    | (have i₁ := eq11826 y
       have i₂ := eq1000 X0
       grind)
    | exact superpose eq1000 eq11826
    | exact resolve eq11826 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000 eq11826
  have eq11956 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) y) := by
    first
    | (have i₁ := eq11906 x
       have i₂ := eq640 sF0 x (M.op x x)
       grind)
    | exact superpose eq640 eq11906
    | exact resolve eq11906 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11906
  have eq11977 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) y) := by
    first
    | (have i₁ := eq11956
       have i₂ := eq1106 sF0 x
       grind)
    | exact superpose eq1106 eq11956
    | exact resolve eq11956 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11956
  have eq11992 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) x) y) := by
    first
    | exact superpose eq1912 eq11977
    | exact resolve eq11977 eq1912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1912 eq11977
  have eq12007 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) X0) X0) y) := by
    intro X0
    first
    | (have i₁ := eq11992
       have i₂ := eq6028 sF0 x x
       grind)
    | (have i₁ := eq11992
       have i₂ := eq6028 sF0 x x
       grind)
    | exact superpose eq6028 eq11992
    | exact resolve eq11992 eq6028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11992
  have eq12058 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1616 eq624
    | (have j0 := eq624 (σ y) X1 X2
       grind)
    | exact resolve eq624 eq1616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624 eq1616
  have eq12059 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1772 eq12058
    | exact resolve eq12058 eq1772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1772 eq12058
  have eq12060 : ∀ X2 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ x)) X2)) (σ y)) := by
    intro X2
    first
    | exact superpose eq4616 eq12059
    | exact resolve eq12059 eq4616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4616 eq12059
  have eq12066 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) (σ y)) := by
    intro X0
    first
    | exact superpose eq1001 eq12060
    | exact resolve eq12060 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001 eq12060
  have eq12116 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq12066 x
       have i₂ := eq640 sF4 sF2 (M.op sF2 x)
       grind)
    | exact superpose eq640 eq12066
    | exact resolve eq12066 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640 eq12066
  have eq12137 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq12116
       have i₂ := eq1106 sF4 sF2
       grind)
    | exact superpose eq1106 eq12116
    | exact resolve eq12116 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106 eq12116
  have eq12152 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1889 eq12137
    | exact resolve eq12137 eq1889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1889 eq12137
  have eq12167 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12152
       have i₂ := eq6028 sF4 sF2 x
       grind)
    | (have i₁ := eq12152
       have i₂ := eq6028 sF4 x sF2
       grind)
    | exact superpose eq6028 eq12152
    | exact resolve eq12152 eq6028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6028 eq12152
  have eq31437 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq84 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31447 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq31437
    | exact resolve eq31437 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31437
  have eq31452 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq31447
       have r₂ := eq27
       grind)
    | exact resolve eq31447 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31447
  have eq31454 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq31452
    | exact resolve eq31452 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31452
  have eq31456 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq31454 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq31454
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq31454
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq31454
       grind)
    | exact resolve eq12 eq31454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31467 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq31454 eq2748
    | exact resolve eq2748 eq31454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31454
  have eq31478 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq31456
  have eq31482 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq6033 eq31467
    | exact resolve eq31467 eq6033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31467
  have eq31485 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq31478
    | exact resolve eq31478 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31478
  have eq31486 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq31485
  have eq32242 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq31482 eq1080
    | exact resolve eq1080 eq31482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080 eq31482
  have eq32260 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq12167 eq32242
    | exact resolve eq32242 eq12167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32242
  have eq36726 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq31486 eq84
    | exact resolve eq84 eq31486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31486
  have eq36740 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq36726
  have eq36758 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36740 eq32260
    | exact resolve eq32260 eq36740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32260 eq36740
  have eq36829 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq36758
  have eq36844 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq36829
       have r₂ := eq27
       grind)
    | exact resolve eq36829 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36829
  have eq36851 : x ≠ x ∨ y = (M.op x y) ∨ (k x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq36844
       grind)
    | exact superpose eq36844 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq36844
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq36844
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq36844
       grind)
    | exact resolve eq12 eq36844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36862 : y = (M.op (M.op x x) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2748 y x
       have i₂ := eq36844
       grind)
    | exact superpose eq36844 eq2748
    | exact resolve eq2748 eq36844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36844
  have eq36873 : y = (M.op x y) ∨ (k x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq36851
  have eq36878 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36862
       have i₂ := eq5925 x
       grind)
    | exact superpose eq5925 eq36862
    | exact resolve eq36862 eq5925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36862
  have eq36881 : y = (M.op x y) ∨ (k x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36873
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq36873
    | exact resolve eq36873 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36873
  have eq36882 : (k x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq36881
  have eq36935 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) X0) X0) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq36878 eq6082
    | exact resolve eq6082 eq36878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36878
  have eq36940 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12007 eq36935
    | exact resolve eq36935 eq12007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36935
  have eq38658 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq36882
       grind)
    | exact superpose eq36882 eq44
    | exact resolve eq44 eq36882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36882
  have eq42564 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq38658
       have i₂ := eq36940
       grind)
    | exact superpose eq36940 eq38658
    | exact resolve eq38658 eq36940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36940 eq38658
  have eq42629 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq42564
  have eq42635 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq42629
    | exact resolve eq42629 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42629
  have eq42646 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq42635 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq42635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42660 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq42646
    | exact resolve eq42646 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42646
  have eq42665 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq42660
       have r₂ := eq27
       grind)
    | exact resolve eq42660 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42660
  have eq42667 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq42665
    | exact resolve eq42665 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42665
  have eq42668 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq42667
  have eq42776 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42668 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq42668
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq42668
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq42668
       grind)
    | exact resolve eq12 eq42668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42787 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42668 eq2748
    | exact resolve eq2748 eq42668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42668
  have eq42798 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq42776
  have eq42803 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6033 eq42787
    | exact resolve eq42787 eq6033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42787
  have eq42806 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq42798
    | exact resolve eq42798 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42798
  have eq42807 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq42806
  have eq42860 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq42803 eq6082
    | exact resolve eq6082 eq42803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42803
  have eq42865 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12167 eq42860
    | exact resolve eq42860 eq12167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42860
  have eq43565 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42807 eq42635
    | exact resolve eq42635 eq42807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42635 eq42807
  have eq43576 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq43565
  have eq43601 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43576 eq42865
    | exact resolve eq42865 eq43576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42865 eq43576
  have eq43675 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq43601
  have eq43692 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq43675
       have r₂ := eq27
       grind)
    | exact resolve eq43675 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43675
  have eq43700 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43692 eq51
    | (have r₁ := eq51
       have r₂ := eq43692
       grind)
    | exact resolve eq51 eq43692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq43692
  have eq43764 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq43700
  have eq43783 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43764 eq55
    | exact resolve eq55 eq43764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq43784 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43764 eq84
    | exact resolve eq84 eq43764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq43764
  have eq43803 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq43784
  have eq43812 : x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq43783
    | exact resolve eq43783 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43783
  have eq43818 : x = (k x y) := by
    first
    | (have r₁ := eq43812
       have r₂ := eq50
       grind)
    | exact resolve eq43812 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq43812
  have eq43823 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq43818
       grind)
    | exact superpose eq43818 eq44
    | exact resolve eq44 eq43818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq43834 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq43818
       grind)
    | exact superpose eq43818 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq43818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43850 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43834
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq43834
    | exact resolve eq43834 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43834
  have eq43859 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq43823
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43823
    | exact resolve eq43823 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43823
  have eq43866 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43850
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq43850
    | exact resolve eq43850 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43850
  have eq43917 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43859 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq43859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43929 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq43917
    | exact resolve eq43917 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43917
  have eq43935 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq43929
    | exact resolve eq43929 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43929
  have eq50282 : y = (M.op (M.op x x) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2748 y x
       have i₂ := eq43803
       grind)
    | exact superpose eq43803 eq2748
    | exact resolve eq2748 eq43803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43803
  have eq50304 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq50282
       have i₂ := eq5925 x
       grind)
    | exact superpose eq5925 eq50282
    | exact resolve eq50282 eq5925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5925 eq50282
  have eq50352 : x ≠ x ∨ y = (M.op x y) ∨ (k x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq43866
       grind)
    | exact superpose eq43866 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq43866
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq43866
       grind)
    | exact resolve eq12 eq43866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43866
  have eq50374 : y = (M.op x y) ∨ (k x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq50352
  have eq50388 : y = (M.op x y) ∨ (k x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq50374
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50374
    | exact resolve eq50374 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50374
  have eq50389 : y = (M.op x y) ∨ (k x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq50388
  have eq50392 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq50389
       have i₂ := eq43818
       grind)
    | exact superpose eq43818 eq50389
    | exact resolve eq50389 eq43818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43818 eq50389
  have eq50551 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) X0) X0) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq50304 eq6082
    | exact resolve eq6082 eq50304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50304
  have eq50561 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq12007 eq50551
    | exact resolve eq50551 eq12007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12007 eq50551
  have eq50856 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43935 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq43935
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq43935
       grind)
    | exact resolve eq12 eq43935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50867 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43935 eq2748
    | exact resolve eq2748 eq43935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2748 eq43935
  have eq50878 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq50856
  have eq50883 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6033 eq50867
    | exact resolve eq50867 eq6033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6033 eq50867
  have eq50886 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq50878
    | exact resolve eq50878 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50878
  have eq50887 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq50886
  have eq50890 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43859 eq50887
    | exact resolve eq50887 eq43859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43859 eq50887
  have eq51998 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq50392
       have i₂ := eq50561
       grind)
    | exact superpose eq50561 eq50392
    | exact resolve eq50392 eq50561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50392 eq50561
  have eq52073 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq51998
  have eq52139 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq52073 eq28
    | exact resolve eq28 eq52073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq52073
  have eq52385 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq52139
    | exact resolve eq52139 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq52139
  have eq52386 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq52385
  have eq52391 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq52386 eq20
    | exact resolve eq20 eq52386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52477 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq52386 eq3305
    | exact resolve eq3305 eq52386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3305 eq52386
  have eq52524 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52477
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52477
    | exact resolve eq52477 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52477
  have eq52589 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52391
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq52391
    | exact resolve eq52391 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq52391
  have eq52930 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq52524
       grind)
    | exact superpose eq52524 eq79
    | exact resolve eq79 eq52524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq52524
  have eq53029 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq52930
  have eq53073 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq53029
    | exact resolve eq53029 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53029
  have eq96102 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq50883 eq6082
    | exact resolve eq6082 eq50883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6082 eq50883
  have eq96109 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12167 eq96102
    | exact resolve eq96102 eq12167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12167 eq96102
  have eq105434 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq96109 eq50890
    | exact resolve eq50890 eq96109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50890 eq96109
  have eq105530 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq105434
  have eq105605 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq105530 eq27
    | exact resolve eq27 eq105530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105631 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq105530 eq3311
    | exact resolve eq3311 eq105530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3311 eq105530
  have eq105741 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq105631
    | exact resolve eq105631 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105631
  have eq105747 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq52589 eq105605
    | (have r₁ := eq105605
       have r₂ := eq52589
       grind)
    | exact resolve eq105605 eq52589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52589 eq105605
  have eq105748 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq105747
  have eq106006 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq105748 eq27
    | exact resolve eq27 eq105748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106030 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq105748 eq3630
    | exact resolve eq3630 eq105748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3630
  have eq106168 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq106030
    | exact resolve eq106030 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq106030
  have eq106854 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq105748 eq106168
    | exact resolve eq106168 eq105748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105748 eq106168
  have eq106871 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq106854
  have eq109282 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106871 eq53073
    | exact resolve eq53073 eq106871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53073 eq106871
  have eq109318 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq109282
  have eq109330 : x = (M.op x y) := by
    first
    | (have r₁ := eq109318
       have r₂ := eq106006
       grind)
    | exact resolve eq109318 eq106006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106006 eq109318
  have eq109345 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq109330 eq20
    | exact resolve eq20 eq109330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq109491 : (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq109330 eq3656
    | exact resolve eq3656 eq109330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3656
  have eq109587 : (M.op x y) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq109491
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq109491
    | exact resolve eq109491 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq109491
  have eq109718 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq109345
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq109345
    | exact resolve eq109345 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109345
  have eq109742 : x = (k x x) := by
    first
    | exact superpose eq109330 eq109587
    | exact resolve eq109587 eq109330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109330 eq109587
  have eq110038 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq109718 eq105741
    | exact resolve eq105741 eq109718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105741
  have eq110048 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq110038
       have r₂ := eq27
       grind)
    | exact resolve eq110038 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110038
  have eq110114 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq838 x x
       have i₂ := eq109742
       grind)
    | exact superpose eq109742 eq838
    | (have j0 := eq838 x x
       grind)
    | exact resolve eq838 eq109742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838 eq109742
  have eq110115 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq110114
  have eq110116 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq110115
  have eq110131 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq110116
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq110116
    | exact resolve eq110116 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq110116
  have eq110152 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq109718 eq110131
    | exact resolve eq110131 eq109718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109718 eq110131
  have eq116522 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq110048 eq110152
    | exact resolve eq110152 eq110048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110048 eq110152
  have eq116523 : False := by grind
  exact eq116523

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pyy_x_pxy_Equation2666 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq37 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
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
  have eq77 : y ≠ (M.op x y) ∨ x = (M.op y x) ∨ x = (k x y) := by
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
  have eq78 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq96 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq101 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq101
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq103
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq103
    | exact resolve eq103 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq136 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq153 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq136
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq136
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq136 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq153
  have eq213 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq638 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) X2)) y) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq639 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) X2)) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq655 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
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
  have eq735 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) X5)) X3) := by
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
  have eq831 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq95 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq95 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq839 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq95 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq840 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq839 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq842 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq831 X0 X1
       have j1 := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq831 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq831 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq831 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq852 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq842 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq842
    | (have j0 := eq842 X0 X1
       grind)
    | exact resolve eq842 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq1061 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) y) := by
    intro X0
    first
    | (have i₁ := eq655 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq655
    | (have j0 := eq655 x y X0
       grind)
    | exact resolve eq655 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1062 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq655
    | (have j0 := eq655 (σ x) (σ y) X0
       grind)
    | exact resolve eq655 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1074 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq655 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq655
    | (have j0 := eq655 x X0 y
       grind)
    | exact resolve eq655 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1075 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq655
    | (have j0 := eq655 (σ x) X0 (σ y)
       grind)
    | exact resolve eq655 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1079 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq655 X0 X1 x
       grind)
    | exact superpose eq655 eq14
    | exact resolve eq14 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1080 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X2)) = (M.op (M.op X0 X0) (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X2)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X0 (M.op X0 X1) X2 X3
       have i₂ := eq655 X0 (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X2)) X3) X1
       grind)
    | exact superpose eq655 eq52
    | exact resolve eq52 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1095 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1080 X0 X1 x X3
       have i₂ := eq655 X0 (M.op X0 X1) x
       grind)
    | exact superpose eq655 eq1080
    | exact resolve eq1080 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080
  have eq1119 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X0) X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1095 x x X3
       have i₂ := eq655 x x x
       grind)
    | exact superpose eq655 eq1095
    | exact resolve eq1095 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095
  have eq1141 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1079 X0 (M.op X0 X1)
       have i₂ := eq655 X0 X0 X1
       grind)
    | exact superpose eq655 eq1079
    | exact resolve eq1079 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1142 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1079 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq1079 X0 (M.op X0 X0)
       grind)
    | exact superpose eq1079 eq1079
    | exact resolve eq1079 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1146 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1 X1 X0
       have i₂ := eq1079 (M.op X0 X1) X0
       grind)
    | exact superpose eq1079 eq55
    | exact resolve eq55 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1151 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X1
       have i₂ := eq1079 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq1079 eq14
    | exact resolve eq14 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1168 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1146 X0 X1
       have i₂ := eq655 X0 X1 X1
       grind)
    | exact superpose eq655 eq1146
    | exact resolve eq1146 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146
  have eq1265 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq1074 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1074
    | (have j0 := eq1074 y
       grind)
    | exact resolve eq1074 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1345 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1265
       have i₂ := eq1061 X0
       grind)
    | exact superpose eq1061 eq1265
    | exact resolve eq1265 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1437 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq26 eq1075
    | (have j0 := eq1075 (σ y)
       grind)
    | exact resolve eq1075 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1475 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1062 eq1437
    | exact resolve eq1437 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1626 : (M.op x x) = (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op x x)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1141 (M.op x x) y
       have i₂ := eq1265
       grind)
    | exact superpose eq1265 eq1141
    | exact resolve eq1141 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1630 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq213 eq1141
    | exact resolve eq1141 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1632 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1437 eq1141
    | exact resolve eq1141 eq1437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437
  have eq1636 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq222 eq1141
    | exact resolve eq1141 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1663 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq1636
       have i₂ := eq1079 sF4 (M.op sF4 sF4)
       grind)
    | exact superpose eq1079 eq1636
    | exact resolve eq1636 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1636
  have eq1667 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1632
       have i₂ := eq1079 sF2 (M.op sF2 sF2)
       grind)
    | exact superpose eq1079 eq1632
    | exact resolve eq1632 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1632
  have eq1669 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1630
       have i₂ := eq1079 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq1079 eq1630
    | exact resolve eq1630 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1630
  have eq1673 : (M.op x x) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1626
       have i₂ := eq1079 x (M.op x x)
       grind)
    | exact superpose eq1079 eq1626
    | exact resolve eq1626 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626
  have eq1704 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1663 eq222
    | exact resolve eq222 eq1663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1713 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1663 eq655
    | exact resolve eq655 eq1663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1721 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq1713 x
       have i₂ := eq655 sF4 sF2 x
       grind)
    | exact superpose eq655 eq1713
    | exact resolve eq1713 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713
  have eq1724 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq1663 eq1721
    | exact resolve eq1721 eq1663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1721
  have eq1727 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq1669 eq213
    | exact resolve eq213 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1736 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1669 eq655
    | exact resolve eq655 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1744 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq1736 x
       have i₂ := eq655 sF0 x x
       grind)
    | exact superpose eq655 eq1736
    | exact resolve eq1736 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1736
  have eq1747 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq1669 eq1744
    | exact resolve eq1744 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1744
  have eq1878 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq1663 eq1667
    | exact resolve eq1667 eq1663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1667
  have eq1879 : (M.op x x) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq1669 eq1673
    | exact resolve eq1673 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673
  have eq2478 : ∀ X0 : G, (M.op (M.op (M.op x y) x) X0) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1669 eq1168
    | exact resolve eq1168 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2480 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1168 (M.op X0 X1) X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq1168
    | exact resolve eq1168 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2482 : x = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | exact superpose eq213 eq1168
    | exact resolve eq1168 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2484 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq222 eq1168
    | exact resolve eq1168 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2488 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1168 (M.op (M.op X0 X0) X0) (M.op X0 X1)
       have i₂ := eq1141 X0 X1
       grind)
    | exact superpose eq1141 eq1168
    | exact resolve eq1168 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2509 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1079 X0 X1
       have i₂ := eq1168 X0 X1
       grind)
    | (have i₁ := eq1079 X1 X1
       have i₂ := eq1168 X1 X1
       grind)
    | exact superpose eq1168 eq1079
    | exact resolve eq1079 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2566 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2488 X0 X1
       have i₂ := eq1151 X0 X0
       grind)
    | exact superpose eq1151 eq2488
    | exact resolve eq2488 eq1151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151 eq2488
  have eq2572 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2566 X0 X1
       have i₂ := eq655 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq655 eq2566
    | exact resolve eq2566 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2566
  have eq2573 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2572 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq2572
    | exact resolve eq2572 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2572
  have eq2716 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) y) X0) x) = (M.op (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) X0) := by
    intro X0
    first
    | exact superpose eq2482 eq655
    | exact resolve eq655 eq2482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2719 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) y) X0) x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) y) X0) := by
    intro X0
    first
    | (have i₁ := eq2716 X0
       have i₂ := eq655 sF0 y y
       grind)
    | exact superpose eq655 eq2716
    | exact resolve eq2716 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2716
  have eq2724 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) y) X0) x) := by
    intro X0
    first
    | exact superpose eq213 eq2719
    | exact resolve eq2719 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2719
  have eq2737 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq2484 eq655
    | exact resolve eq655 eq2484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2738 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) (M.op (M.op (σ x) (σ y)) (σ y))) (σ x)) := by
    first
    | exact superpose eq2484 eq1141
    | exact resolve eq1141 eq2484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2739 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq2738
       have i₂ := eq655 sF4 sF3 sF3
       grind)
    | exact superpose eq655 eq2738
    | exact resolve eq2738 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2738
  have eq2740 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq2737 X0
       have i₂ := eq655 sF4 sF3 sF3
       grind)
    | exact superpose eq655 eq2737
    | exact resolve eq2737 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2737
  have eq2744 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) (σ x)) := by
    first
    | exact superpose eq222 eq2739
    | exact resolve eq2739 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2739
  have eq2745 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq222 eq2740
    | exact resolve eq2740 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2740
  have eq2748 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq2744
       have i₂ := eq1168 sF2 (M.op sF4 sF3)
       grind)
    | exact superpose eq1168 eq2744
    | exact resolve eq2744 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2744
  have eq3024 : (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = (M.op (M.op (M.op x y) y) x) := by
    first
    | exact superpose eq2482 eq2573
    | exact resolve eq2573 eq2482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3033 : (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq2484 eq2573
    | exact resolve eq2573 eq2484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3043 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq2573
    | (have j0 := eq2573 (σ x) (σ y)
       grind)
    | exact resolve eq2573 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3097 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq3033
       have i₂ := eq655 sF4 sF3 sF3
       grind)
    | exact superpose eq655 eq3033
    | exact resolve eq3033 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3033
  have eq3106 : (M.op (M.op (M.op x y) (M.op x y)) y) = (M.op (M.op (M.op x y) y) x) := by
    first
    | (have i₁ := eq3024
       have i₂ := eq655 sF0 y y
       grind)
    | exact superpose eq655 eq3024
    | exact resolve eq3024 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3024
  have eq3132 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq222 eq3097
    | exact resolve eq3097 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3097
  have eq3140 : x = (M.op (M.op (M.op x y) y) x) := by
    first
    | exact superpose eq213 eq3106
    | exact resolve eq3106 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3106
  have eq3347 : (σ x) ≠ (σ x) ∨ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq3132 eq13
    | (have j0 := eq13 (σ x) (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | (have r₁ := eq13 (σ x) (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq3132
       grind)
    | exact resolve eq13 eq3132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3132
  have eq3359 : (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) := by grind
  clear eq3347
  have eq3367 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq3359
       have i₂ := eq655 sF4 sF3 sF3
       grind)
    | exact superpose eq655 eq3359
    | exact resolve eq3359 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3359
  have eq3372 : (σ x) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq222 eq3367
    | exact resolve eq3367 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3367
  have eq3515 : x ≠ x ∨ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = (k x (M.op (M.op x y) y)) := by
    first
    | exact superpose eq3140 eq13
    | (have j0 := eq13 x (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq13 x (M.op (M.op x y) y)
       have r₂ := eq3140
       grind)
    | exact resolve eq13 eq3140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3140
  have eq3527 : (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = (k x (M.op (M.op x y) y)) := by grind
  clear eq3515
  have eq3535 : (M.op (M.op (M.op x y) (M.op x y)) y) = (k x (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq3527
       have i₂ := eq655 sF0 y y
       grind)
    | exact superpose eq655 eq3527
    | exact resolve eq3527 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3527
  have eq3540 : x = (k x (M.op (M.op x y) y)) := by
    first
    | exact superpose eq213 eq3535
    | exact resolve eq3535 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq3535
  have eq3550 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq840 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq840
    | (have j0 := eq840 (τ X0)
       grind)
    | exact resolve eq840 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq840
  have eq3558 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3550 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3550
    | (have j0 := eq3550 X0
       grind)
    | exact resolve eq3550 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3550
  have eq3564 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3558 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3558
    | (have j0 := eq3558 X0
       grind)
    | exact resolve eq3558 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3558
  have eq3662 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) y) := by
    intro X1
    first
    | exact superpose eq1345 eq217
    | (have j0 := eq217 y X1
       grind)
    | exact resolve eq217 eq1345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq3663 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) y) := by
    intro X1
    first
    | exact superpose eq1669 eq3662
    | exact resolve eq3662 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3662
  have eq3960 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1475 eq226
    | (have j0 := eq226 (σ y) X1
       grind)
    | exact resolve eq226 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq3961 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1663 eq3960
    | exact resolve eq3960 eq1663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3960
  have eq4012 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2480 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq2480 X0 X1
       grind)
    | exact superpose eq2480 eq2480
    | exact resolve eq2480 eq2480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4018 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq3663 eq2480
    | exact resolve eq2480 eq3663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3663
  have eq4020 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq3961 eq2480
    | exact resolve eq2480 eq3961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3961
  have eq4028 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq2482 eq2480
    | exact resolve eq2480 eq2482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2482
  have eq4040 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq2484 eq2480
    | exact resolve eq2480 eq2484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4078 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2573 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq2480 X0 X1
       grind)
    | exact superpose eq2480 eq2573
    | exact resolve eq2573 eq2480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4079 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4078 X0 X1
       have i₂ := eq655 (M.op X0 X1) X1 X1
       grind)
    | exact superpose eq655 eq4078
    | exact resolve eq4078 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4078
  have eq4102 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq4040
       have i₂ := eq1168 sF2 sF4
       grind)
    | exact superpose eq1168 eq4040
    | exact resolve eq4040 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4040
  have eq4111 : (M.op (M.op x y) y) = (M.op (M.op x x) (M.op x y)) := by
    first
    | (have i₁ := eq4028
       have i₂ := eq1168 x sF0
       grind)
    | exact superpose eq1168 eq4028
    | exact resolve eq4028 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4028
  have eq4118 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq1704 eq4020
    | exact resolve eq4020 eq1704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4020
  have eq4120 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op x (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq1727 eq4018
    | exact resolve eq4018 eq1727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727 eq4018
  have eq4124 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4012 X0 X1
       have i₂ := eq1168 X0 (M.op X0 X1)
       grind)
    | exact superpose eq1168 eq4012
    | exact resolve eq4012 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4012
  have eq4139 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4079 X0 X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq4079
    | exact resolve eq4079 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4079
  have eq4155 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq1075 eq4102
    | exact resolve eq4102 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075 eq4102
  have eq4160 : (M.op (M.op x y) y) = (M.op (M.op x x) x) := by
    first
    | exact superpose eq1074 eq4111
    | exact resolve eq4111 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074 eq4111
  have eq4164 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq1878 eq4118
    | exact resolve eq4118 eq1878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878 eq4118
  have eq4165 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op (M.op x y) x) X0)) := by
    intro X0
    first
    | exact superpose eq1879 eq4120
    | exact resolve eq4120 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879 eq4120
  have eq4167 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4124 X0 X1
       have i₂ := eq655 X0 X0 X1
       grind)
    | exact superpose eq655 eq4124
    | exact resolve eq4124 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4124
  have eq5780 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq96 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq96
    | (have j0 := eq96 x
       grind)
    | exact resolve eq96 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq5813 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5780
  have eq5821 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5813
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq5813
    | exact resolve eq5813 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq5813
  have eq5837 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq5821
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq5821 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5821
  have eq5842 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5837 eq49
    | exact resolve eq49 eq5837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq6214 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq137
    | (have j0 := eq137 (M.op x y)
       grind)
    | exact resolve eq137 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq6235 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq6214
  have eq6238 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq136 eq6235
    | exact resolve eq6235 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq6235
  have eq6262 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq6238
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6238 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6238
  have eq6903 : (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq2748 eq13
    | (have j0 := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ x))
       grind)
    | (have r₁ := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ x))
       have r₂ := eq2748
       grind)
    | exact resolve eq13 eq2748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2748
  have eq6920 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ x))) := by grind
  clear eq6903
  have eq6933 : (M.op (M.op (σ x) (σ x)) (σ x)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq6920
       have i₂ := eq655 sF2 sF2 sF2
       grind)
    | exact superpose eq655 eq6920
    | exact resolve eq6920 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6920
  have eq6944 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq4155 eq6933
    | exact resolve eq6933 eq4155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6933
  have eq7273 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2478 eq4165
    | exact resolve eq4165 eq2478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2478
  have eq7334 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4167 X0 X2
       have i₂ := eq4167 X0 X1
       grind)
    | (have i₁ := eq4167 X1 X1
       have i₂ := eq4167 X1 X1
       grind)
    | exact superpose eq4167 eq4167
    | exact resolve eq4167 eq4167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7338 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq4167 x X0
       have i₂ := eq4160
       grind)
    | exact superpose eq4160 eq4167
    | exact resolve eq4167 eq4160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4160
  have eq7339 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq4155 eq4167
    | exact resolve eq4167 eq4155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4155
  have eq7391 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1141 X0 X2
       have i₂ := eq4167 X0 X1
       grind)
    | (have i₁ := eq1141 X1 X1
       have i₂ := eq4167 X1 X1
       grind)
    | exact superpose eq4167 eq1141
    | exact resolve eq1141 eq4167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141 eq4167
  have eq7617 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) y) (M.op (M.op x X0) X1)) = (M.op (M.op (M.op x X0) (M.op x X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq655 (M.op x X0) X0 X1
       have i₂ := eq7338 X0
       grind)
    | (have i₁ := eq655 (M.op x y) y x
       have i₂ := eq7338 X0
       grind)
    | exact superpose eq7338 eq655
    | exact resolve eq655 eq7338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7630 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) y) (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7617 X0 X1
       have i₂ := eq14 x X0 X0
       grind)
    | exact superpose eq14 eq7617
    | exact resolve eq7617 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7617
  have eq7696 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) X0) X1)) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) X0)) X0) := by
    intro X0 X1
    first
    | exact superpose eq7339 eq655
    | exact resolve eq655 eq7339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7709 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7696 x X1
       have i₂ := eq14 sF2 x x
       grind)
    | exact superpose eq14 eq7696
    | exact resolve eq7696 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7696
  have eq9911 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1345 eq638
    | (have j0 := eq638 y X1 X2
       grind)
    | exact resolve eq638 eq1345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638 eq1345
  have eq9912 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) x) X1)) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1669 eq9911
    | exact resolve eq9911 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9911
  have eq9913 : ∀ X2 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x x) X2)) y) := by
    intro X2
    first
    | exact superpose eq4165 eq9912
    | exact resolve eq9912 eq4165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4165 eq9912
  have eq9986 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x y) (M.op x X0))) y) := by
    intro X0
    first
    | (have i₁ := eq9913 y
       have i₂ := eq1061 X0
       grind)
    | exact superpose eq1061 eq9913
    | exact resolve eq9913 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9913
  have eq10025 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) y) := by
    first
    | (have i₁ := eq9986 x
       have i₂ := eq655 sF0 x (M.op x x)
       grind)
    | exact superpose eq655 eq9986
    | exact resolve eq9986 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9986
  have eq10041 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) y) := by
    first
    | (have i₁ := eq10025
       have i₂ := eq1168 sF0 x
       grind)
    | exact superpose eq1168 eq10025
    | exact resolve eq10025 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10025
  have eq10053 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) x) y) := by
    first
    | exact superpose eq1747 eq10041
    | exact resolve eq10041 eq1747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747 eq10041
  have eq10174 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1475 eq639
    | (have j0 := eq639 (σ y) X1 X2
       grind)
    | exact resolve eq639 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639 eq1475
  have eq10175 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1663 eq10174
    | exact resolve eq10174 eq1663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1663 eq10174
  have eq10176 : ∀ X2 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ x)) X2)) (σ y)) := by
    intro X2
    first
    | exact superpose eq4164 eq10175
    | exact resolve eq10175 eq4164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4164 eq10175
  have eq10185 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) (σ y)) := by
    intro X0
    first
    | exact superpose eq1062 eq10176
    | exact resolve eq10176 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062 eq10176
  have eq10224 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq10185 x
       have i₂ := eq655 sF4 sF2 (M.op sF2 x)
       grind)
    | exact superpose eq655 eq10185
    | exact resolve eq10185 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10185
  have eq10240 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq10224
       have i₂ := eq1168 sF4 sF2
       grind)
    | exact superpose eq1168 eq10224
    | exact resolve eq10224 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10224
  have eq10252 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1724 eq10240
    | exact resolve eq10240 eq1724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724 eq10240
  have eq10795 : ∀ X0 : G, x = (M.op (M.op (M.op x x) x) (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq7273 eq2509
    | exact resolve eq2509 eq7273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2509 eq7273
  have eq10801 : ∀ X0 : G, x = (M.op (M.op (M.op x y) y) (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq10795 X0
       have i₂ := eq7338 x
       grind)
    | exact superpose eq7338 eq10795
    | exact resolve eq10795 eq7338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10795
  have eq11265 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) X0) X0) y) := by
    intro X0
    first
    | (have i₁ := eq10053
       have i₂ := eq7334 sF0 x x
       grind)
    | (have i₁ := eq10053
       have i₂ := eq7334 sF0 x x
       grind)
    | exact superpose eq7334 eq10053
    | exact resolve eq10053 eq7334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10053
  have eq11285 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10252
       have i₂ := eq7334 sF4 sF2 x
       grind)
    | (have i₁ := eq10252
       have i₂ := eq7334 sF4 x sF2
       grind)
    | exact superpose eq7334 eq10252
    | exact resolve eq10252 eq7334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7334 eq10252
  have eq17249 : ∀ X0 X1 : G, (M.op x x) = (M.op x (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq7630 eq2724
    | exact resolve eq2724 eq7630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2724 eq7630
  have eq17355 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq7709 eq2745
    | exact resolve eq2745 eq7709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2745 eq7709
  have eq27769 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) X5)) X3) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq735 X0 X1 x X3 X4 X5
       have i₂ := eq655 X0 X1 x
       grind)
    | exact superpose eq655 eq735
    | exact resolve eq735 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq27877 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2)) X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq27769 (M.op X0 X2) (M.op X0 X2) X0 x x
       have i₂ := eq55 X0 X2 X2 (M.op X0 X2)
       grind)
    | exact superpose eq55 eq27769
    | exact resolve eq27769 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq27769
  have eq28023 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op X0 X1)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op X0 X1)) X3)) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq27877 X0 X1 x X3
       have i₂ := eq655 (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1) x
       grind)
    | exact superpose eq655 eq27877
    | exact resolve eq27877 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27877
  have eq28155 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) X3)) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq28023 X0 X1 X3
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq28023
    | exact resolve eq28023 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28023
  have eq28250 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq28155 X0 X1 x
       have i₂ := eq655 (M.op X0 X1) (M.op X0 X1) x
       grind)
    | exact superpose eq655 eq28155
    | exact resolve eq28155 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28155
  have eq28323 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq28250 X0 X1
       have i₂ := eq655 X0 X1 X1
       grind)
    | exact superpose eq655 eq28250
    | exact resolve eq28250 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28250
  have eq34040 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5837 eq112
    | exact resolve eq112 eq5837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq5837
  have eq34110 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq118 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq34110
    | exact resolve eq34110 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34110
  have eq34127 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq34120
       have r₂ := eq27
       grind)
    | exact resolve eq34120 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34120
  have eq34129 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq34127
    | exact resolve eq34127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34127
  have eq34142 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq34129 eq2480
    | exact resolve eq2480 eq34129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34129
  have eq34158 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq7339 eq34142
    | exact resolve eq34142 eq7339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34142
  have eq34317 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq34158 eq3372
    | exact resolve eq3372 eq34158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3372 eq34158
  have eq35249 : (τ (σ x)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq34317 eq59
    | exact resolve eq59 eq34317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34317
  have eq35269 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq35249
    | exact resolve eq35249 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35249
  have eq35273 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq35269
       have r₂ := eq77
       grind)
    | exact resolve eq35269 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq35269
  have eq35274 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1669 eq160
    | exact resolve eq160 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq35275 : (σ (M.op (M.op x y) x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq6262 eq35274
    | exact resolve eq35274 eq6262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6262 eq35274
  have eq35276 : (σ (M.op (M.op x y) x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1669 eq35275
    | exact resolve eq35275 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35275
  have eq35278 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq35273
       grind)
    | exact superpose eq35273 eq44
    | exact resolve eq44 eq35273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq35285 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq35273
       grind)
    | exact superpose eq35273 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq35273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35273
  have eq35294 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq35285
  have eq35303 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35294
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35294
    | exact resolve eq35294 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35294
  have eq35310 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq35278
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35278
    | exact resolve eq35278 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35278
  have eq35319 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35303
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35303
    | exact resolve eq35303 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35303
  have eq35381 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq35310 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq35310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35310
  have eq35395 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq35381
    | exact resolve eq35381 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35381
  have eq35403 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq35395
    | exact resolve eq35395 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35395
  have eq35404 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq35403
  have eq35457 : y = (M.op (M.op x x) x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2480 y x
       have i₂ := eq35319
       grind)
    | exact superpose eq35319 eq2480
    | exact resolve eq2480 eq35319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35461 : y = (M.op (M.op x x) y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4139 y x
       have i₂ := eq35319
       grind)
    | exact superpose eq35319 eq4139
    | exact resolve eq4139 eq35319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35319
  have eq35471 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35461
       have i₂ := eq1265
       grind)
    | exact superpose eq1265 eq35461
    | exact resolve eq35461 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35461
  have eq35474 : y = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35457
       have i₂ := eq7338 x
       grind)
    | exact superpose eq7338 eq35457
    | exact resolve eq35457 eq7338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7338 eq35457
  have eq35479 : y = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1669 eq35471
    | exact resolve eq35471 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35471
  have eq35792 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) X0) X0) y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq35474 eq7391
    | exact resolve eq7391 eq35474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7391 eq35474
  have eq35797 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11265 eq35792
    | exact resolve eq35792 eq11265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35792
  have eq38290 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq35404 eq2480
    | exact resolve eq2480 eq35404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35404
  have eq38306 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq7339 eq38290
    | exact resolve eq38290 eq7339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38290
  have eq44192 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq34040
       have i₂ := eq35797
       grind)
    | exact superpose eq35797 eq34040
    | exact resolve eq34040 eq35797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35797
  have eq44254 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq44192
  have eq44265 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq44254
    | exact resolve eq44254 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44254
  have eq44317 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq44265 eq17355
    | exact resolve eq17355 eq44265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17355 eq44265
  have eq44783 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35479 eq35276
    | exact resolve eq35276 eq35479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35276 eq35479
  have eq44848 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq44783
  have eq44855 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44848
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44848
    | exact resolve eq44848 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44848
  have eq44921 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44855 eq1142
    | exact resolve eq1142 eq44855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142 eq44855
  have eq51458 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44921 eq44317
    | exact resolve eq44317 eq44921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44317 eq44921
  have eq51516 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq51458
  have eq51542 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq51516
    | exact resolve eq51516 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51516
  have eq51553 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq51542
       have r₂ := eq27
       grind)
    | exact resolve eq51542 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51542
  have eq51562 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq51553 eq78
    | (have r₁ := eq78
       have r₂ := eq51553
       grind)
    | exact resolve eq78 eq51553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq51572 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq51553 eq1704
    | exact resolve eq1704 eq51553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51587 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq51553 eq3043
    | exact resolve eq3043 eq51553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3043
  have eq51623 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ y) X0) X0) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq51553 eq11285
    | exact resolve eq11285 eq51553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11285 eq51553
  have eq51628 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq51562
  have eq51630 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq51623 x
       have i₂ := eq4139 sF3 x
       grind)
    | exact superpose eq4139 eq51623
    | exact resolve eq51623 eq4139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51623
  have eq51634 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq51587
    | exact resolve eq51587 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51587
  have eq51661 : (τ (σ y)) = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq51630 eq5842
    | exact resolve eq5842 eq51630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51665 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq51630 eq6944
    | exact resolve eq6944 eq51630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6944 eq51630
  have eq51771 : y = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq51661
    | exact resolve eq51661 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq51661
  have eq51792 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq51634 eq5842
    | exact resolve eq5842 eq51634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5842
  have eq51826 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq51634 eq1079
    | exact resolve eq1079 eq51634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52216 : y = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq51771
       have i₂ := eq51792
       grind)
    | exact superpose eq51792 eq51771
    | exact resolve eq51771 eq51792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51771
  have eq52217 : x ≠ (τ (M.op (σ x) (σ y))) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3564 x
       have i₂ := eq51792
       grind)
    | exact superpose eq51792 eq3564
    | (have j0 := eq3564 x
       grind)
    | exact resolve eq3564 eq51792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3564 eq51792
  have eq52237 : y = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq52216
  have eq138719 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq51628 eq59
    | exact resolve eq59 eq51628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq51628
  have eq138751 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq138719
    | exact resolve eq138719 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138719
  have eq139536 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq138751 eq51572
    | exact resolve eq51572 eq138751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51572 eq138751
  have eq139684 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (k x y) := by grind
  clear eq139536
  have eq139725 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq139684
    | exact resolve eq139684 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139684
  have eq139765 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq139725
       grind)
    | exact superpose eq139725 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq139725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139725
  have eq139785 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq139765
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq139765
    | exact resolve eq139765 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139765
  have eq139786 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq139785
  have eq139809 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq139786
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq139786
    | exact resolve eq139786 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139786
  have eq139810 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq139809
  have eq140640 : x = (M.op (M.op (M.op (M.op y y) x) x) y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28323 y x
       have i₂ := eq139810
       grind)
    | exact superpose eq139810 eq28323
    | exact resolve eq28323 eq139810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28323 eq139810
  have eq140656 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq140640
       have i₂ := eq1079 y x
       grind)
    | exact superpose eq1079 eq140640
    | exact resolve eq140640 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079 eq140640
  have eq140691 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op x y) X0)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1119 y x
       have i₂ := eq140656
       grind)
    | exact superpose eq140656 eq1119
    | exact resolve eq1119 eq140656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119 eq140656
  have eq140785 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq140691 x
       have i₂ := eq17249 y x
       grind)
    | exact superpose eq17249 eq140691
    | exact resolve eq140691 eq17249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140691
  have eq140797 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq140785
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq140785
    | exact resolve eq140785 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140785
  have eq142429 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq34040
       have i₂ := eq140797
       grind)
    | exact superpose eq140797 eq34040
    | exact resolve eq34040 eq140797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140797
  have eq142524 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq142429
  have eq142556 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq142524
    | exact resolve eq142524 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142524
  have eq146947 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq142556 eq51634
    | exact resolve eq51634 eq142556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51634 eq142556
  have eq147088 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq146947
  have eq147121 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq147088
       have r₂ := eq27
       grind)
    | exact resolve eq147088 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147088
  have eq147134 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq147121 eq27
    | exact resolve eq27 eq147121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147232 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq147121 eq51826
    | exact resolve eq51826 eq147121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51826
  have eq147236 : x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq147121 eq52217
    | exact resolve eq52217 eq147121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52217
  have eq147237 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq147121 eq52237
    | exact resolve eq52237 eq147121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52237 eq147121
  have eq147524 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq147237
  have eq147525 : x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq147236
  have eq147529 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq147232 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147232
  have eq147610 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq147524
    | exact resolve eq147524 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147524
  have eq147611 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq147525
       have r₂ := eq28
       grind)
    | exact resolve eq147525 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq147525
  have eq147614 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7339 eq147529
    | (have j0 := eq147529 (σ y)
       grind)
    | exact resolve eq147529 eq7339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7339 eq147529
  have eq149639 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq147610 eq20
    | exact resolve eq20 eq147610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149819 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op y X0) X0) y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq147610 eq11265
    | exact resolve eq11265 eq147610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11265 eq147610
  have eq149860 : y = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq149819 x
       have i₂ := eq4139 y x
       grind)
    | exact superpose eq4139 eq149819
    | exact resolve eq149819 eq4139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149819
  have eq149981 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq149639
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq149639
    | exact resolve eq149639 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149639
  have eq152877 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1061 x
       have i₂ := eq147611
       grind)
    | exact superpose eq147611 eq1061
    | exact resolve eq1061 eq147611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061 eq147611
  have eq153007 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq152877
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq152877
    | exact resolve eq152877 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152877
  have eq153681 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq147614 eq51665
    | exact resolve eq51665 eq147614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51665 eq147614
  have eq153758 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq153681
  have eq159270 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq34040
       have i₂ := eq149860
       grind)
    | exact superpose eq149860 eq34040
    | exact resolve eq34040 eq149860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34040 eq149860
  have eq159373 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq159270
  have eq159395 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq159373
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq159373
    | exact resolve eq159373 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159373
  have eq164071 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq153758 eq118
    | exact resolve eq118 eq153758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq153758
  have eq164090 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq164071
  have eq164101 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq164090
       have r₂ := eq147134
       grind)
    | exact resolve eq164090 eq147134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147134 eq164090
  have eq170058 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq159395 eq2573
    | exact resolve eq2573 eq159395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2573 eq159395
  have eq170102 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq170058
    | exact resolve eq170058 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170058
  have eq170247 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq170102 eq27
    | exact resolve eq27 eq170102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170102
  have eq170638 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq170247
       have r₂ := eq149981
       grind)
    | exact resolve eq170247 eq149981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149981 eq170247
  have eq251874 : y = (M.op (M.op x x) y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4139 y x
       have i₂ := eq164101
       grind)
    | exact superpose eq164101 eq4139
    | exact resolve eq4139 eq164101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164101
  have eq251904 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq251874
       have i₂ := eq1265
       grind)
    | exact superpose eq1265 eq251874
    | exact resolve eq251874 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251874
  have eq251915 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1669 eq251904
    | exact resolve eq251904 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251904
  have eq259991 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq251915 eq153007
    | exact resolve eq153007 eq251915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153007 eq251915
  have eq260061 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq259991
  have eq260396 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq260061
  have eq260403 : x = (M.op x y) := by
    first
    | (have r₁ := eq260396
       have r₂ := eq170638
       grind)
    | exact resolve eq260396 eq170638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170638 eq260396
  have eq260590 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq260403 eq20
    | exact resolve eq20 eq260403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq260752 : x = (k x (M.op x y)) := by
    first
    | exact superpose eq260403 eq3540
    | exact resolve eq3540 eq260403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3540
  have eq260794 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op x X0) x)) := by
    intro X0
    first
    | exact superpose eq260403 eq10801
    | exact resolve eq10801 eq260403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10801
  have eq260902 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op x X0) x)) := by
    intro X0
    first
    | (have i₁ := eq260794 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq260794
    | (have j0 := eq260794 X0
       grind)
    | exact resolve eq260794 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260794
  have eq260917 : x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq260752
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq260752
    | exact resolve eq260752 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq260752
  have eq261059 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq260590
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq260590
    | exact resolve eq260590 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260590
  have eq261074 : ∀ X0 : G, x = (M.op x (M.op (M.op x X0) x)) := by
    intro X0
    first
    | exact superpose eq260403 eq260902
    | exact resolve eq260902 eq260403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260902
  have eq261087 : x = (k x x) := by
    first
    | exact superpose eq260403 eq260917
    | exact resolve eq260917 eq260403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260917
  have eq261123 : x = (M.op x x) := by
    first
    | (have i₁ := eq261074 x
       have i₂ := eq17249 x x
       grind)
    | exact superpose eq17249 eq261074
    | exact resolve eq261074 eq17249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17249 eq261074
  have eq261995 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq261059 eq26
    | exact resolve eq26 eq261059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq262041 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq261059 eq1704
    | exact resolve eq1704 eq261059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1704
  have eq262518 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq852 x x
       have i₂ := eq261087
       grind)
    | exact superpose eq261087 eq852
    | (have j0 := eq852 x x
       grind)
    | exact resolve eq852 eq261087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852 eq261087
  have eq262521 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq262518
  have eq262522 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq262521
  have eq262544 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq262522
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq262522
    | exact resolve eq262522 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262522
  have eq262575 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq261059 eq262544
    | exact resolve eq262544 eq261059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262544
  have eq269029 : (M.op (M.op (σ (M.op x y)) (σ y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq262041 eq2480
    | exact resolve eq2480 eq262041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2480
  have eq269056 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq269029
       have i₂ := eq1168 sF1 sF3
       grind)
    | exact superpose eq1168 eq269029
    | exact resolve eq269029 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168 eq269029
  have eq269079 : (M.op (σ (M.op x y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq262575 eq269056
    | exact resolve eq269056 eq262575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262575 eq269056
  have eq269095 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq261995 eq269079
    | exact resolve eq269079 eq261995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269079
  have eq269587 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq269095 eq262041
    | exact resolve eq262041 eq269095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262041
  have eq269743 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq269587 eq2484
    | exact resolve eq2484 eq269587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2484
  have eq269827 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq269587 eq655
    | exact resolve eq655 eq269587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq269871 : ∀ X0 : G, (σ x) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq222 eq269827
    | exact resolve eq269827 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq269827
  have eq269908 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq261059 eq269743
    | exact resolve eq269743 eq261059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269743
  have eq269927 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq261059 eq269871
    | exact resolve eq269871 eq261059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269871
  have eq277851 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq38306 eq269927
    | exact resolve eq269927 eq38306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38306 eq269927
  have eq277967 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq261995 eq277851
    | exact resolve eq277851 eq261995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277851
  have eq277997 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq277967
       have r₂ := eq27
       grind)
    | exact resolve eq277967 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277967
  have eq278010 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq261059 eq277997
    | exact resolve eq277997 eq261059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277997
  have eq278017 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq278010
       have r₂ := eq27
       grind)
    | exact resolve eq278010 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278010
  have eq278866 : y = (M.op (M.op x x) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4139 y x
       have i₂ := eq278017
       grind)
    | exact superpose eq278017 eq4139
    | exact resolve eq4139 eq278017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4139 eq278017
  have eq278902 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq278866
       have i₂ := eq1265
       grind)
    | exact superpose eq1265 eq278866
    | exact resolve eq278866 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265 eq278866
  have eq278914 : y = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1669 eq278902
    | exact resolve eq278902 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669 eq278902
  have eq278920 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq260403 eq278914
    | exact resolve eq278914 eq260403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260403 eq278914
  have eq278923 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq278920
       have i₂ := eq261123
       grind)
    | exact superpose eq261123 eq278920
    | exact resolve eq278920 eq261123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261123 eq278920
  have eq279217 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq278923 eq269908
    | exact resolve eq269908 eq278923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269908 eq278923
  have eq279264 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq261995 eq279217
    | exact resolve eq279217 eq261995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261995 eq279217
  have eq279377 : x = y := by
    first
    | (have r₁ := eq279264
       have r₂ := eq27
       grind)
    | exact resolve eq279264 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279264
  have eq279472 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq279377
       grind)
    | exact superpose eq279377 eq24
    | exact resolve eq24 eq279377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq279377
  have eq279988 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq279472
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq279472
    | exact resolve eq279472 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq279472
  have eq280162 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq261059 eq279988
    | exact resolve eq279988 eq261059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261059 eq279988
  have eq280855 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq280162 eq269587
    | exact resolve eq269587 eq280162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269587 eq280162
  have eq280865 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq269095 eq280855
    | exact resolve eq280855 eq269095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269095 eq280855
  have eq280974 : False := by grind
  exact eq280974

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pxy_x_pyx_Equation2666 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
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
  clear eq18
  have eq28 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  clear eq23
  have eq440 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 X0)) = (M.op (M.op X1 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 X2 X0 X2
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq54
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq454 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op (M.op X1 X2) (M.op X1 X0)) X3)) = (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X0)) (M.op (M.op X1 X2) (M.op X1 X0))) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq440 X3 (M.op (M.op X1 X2) (M.op X1 X0)) X2
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq440
    | exact resolve eq440 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X0)) X3) X1) = (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X0)) (M.op (M.op X1 X2) (M.op X1 X0))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq440 X2 (M.op (M.op X1 X2) (M.op X1 X0)) X3
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq440
    | exact resolve eq440 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X2 X0) (M.op X2 X0)) X3) = (M.op (M.op (M.op X2 X0) X3) (M.op (M.op X2 X2) X0)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq440 (M.op X2 x) (M.op X2 X0) X3
       have i₂ := eq440 x X2 X0
       grind)
    | exact superpose eq440 eq440
    | exact resolve eq440 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq468 : ∀ X0 X2 : G, (M.op (M.op (M.op X2 X2) X0) X0) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq440 x X2 X0
       grind)
    | exact superpose eq440 eq9
    | exact resolve eq9 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X2 X0) X3) (M.op (M.op X2 X2) X0)) = (M.op (M.op (M.op X2 X2) X0) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq462 X0 X2 X3
       have i₂ := eq440 X0 X2 X0
       grind)
    | exact superpose eq440 eq462
    | exact resolve eq462 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq478 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X0)) X3) X1) = (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X2)) (M.op X1 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq460 X0 X1 X2 X3
       have i₂ := eq440 (M.op X1 X0) (M.op X1 X2) (M.op X1 X0)
       grind)
    | exact superpose eq440 eq460
    | exact resolve eq460 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq481 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op (M.op X1 X2) (M.op X1 X0)) X3)) = (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X2)) (M.op X1 X0)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq454 X0 X1 X2 X3
       have i₂ := eq440 (M.op X1 X0) (M.op X1 X2) (M.op X1 X0)
       grind)
    | exact superpose eq440 eq454
    | exact resolve eq454 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq485 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X0)) X3) X1) = (M.op (M.op (M.op (M.op X1 X1) X2) (M.op X1 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq478 X0 X1 X2 X3
       have i₂ := eq440 X2 X1 X2
       grind)
    | exact superpose eq440 eq478
    | exact resolve eq478 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq487 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op (M.op X1 X2) (M.op X1 X0)) X3)) = (M.op (M.op (M.op (M.op X1 X1) X2) (M.op X1 X0)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq481 X0 X1 X2 X3
       have i₂ := eq440 X2 X1 X2
       grind)
    | exact superpose eq440 eq481
    | exact resolve eq481 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq488 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X1) X2) (M.op X1 X0)) X3) = (M.op (M.op (M.op (M.op X1 X1) X2) X3) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq485 X0 X1 X2 X3
       have i₂ := eq440 X0 X1 X2
       grind)
    | exact superpose eq440 eq485
    | exact resolve eq485 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq489 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X1) X2) (M.op X1 X0)) X2) = (M.op X1 (M.op (M.op (M.op X1 X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq487 X0 X1 X2 X3
       have i₂ := eq440 X0 X1 X2
       grind)
    | exact superpose eq440 eq487
    | exact resolve eq487 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq490 : ∀ X1 X2 X3 : G, (M.op X1 (M.op (M.op (M.op X1 X1) X2) X3)) = (M.op (M.op (M.op (M.op X1 X1) X2) X2) X1) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq489 x X1 X2 X3
       have i₂ := eq488 x X1 X2 X2
       grind)
    | exact superpose eq488 eq489
    | exact resolve eq489 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq491 : ∀ X1 X2 X3 : G, (M.op X1 X1) = (M.op X1 (M.op (M.op (M.op X1 X1) X2) X3)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq490 X1 X2 X3
       have i₂ := eq468 X2 X1
       grind)
    | (have i₁ := eq490 X1 X2 X3
       have i₂ := eq468 x (M.op (M.op (M.op X1 X1) X2) X2)
       grind)
    | exact superpose eq468 eq490
    | exact resolve eq490 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq493 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op X1 X1) X0) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq468 X2 (M.op X1 X0)
       have i₂ := eq440 X0 X1 X0
       grind)
    | exact superpose eq440 eq468
    | exact resolve eq468 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq496 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq468 (M.op X0 X1) X0
       have i₂ := eq440 X1 X0 X0
       grind)
    | exact superpose eq440 eq468
    | exact resolve eq468 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq440 X1 (M.op (M.op X0 X0) X1) X2
       have i₂ := eq468 X1 X0
       grind)
    | exact superpose eq468 eq440
    | exact resolve eq440 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq505 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq502 X0 X1 X2
       have i₂ := eq440 X1 (M.op X0 X0) X1
       grind)
    | exact superpose eq440 eq502
    | exact resolve eq502 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq509 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq505 X0 X1 X2
       have i₂ := eq440 X0 X0 X0
       grind)
    | exact superpose eq440 eq505
    | exact resolve eq505 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq522 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) = (M.op X0 (M.op (M.op (M.op X0 X0) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq440 X2 (M.op (M.op X0 X0) X0) (M.op X0 X1)
       have i₂ := eq496 X0 X1
       grind)
    | exact superpose eq496 eq440
    | exact resolve eq440 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq523 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq522 X0 X1 x
       have i₂ := eq491 X0 X0 x
       grind)
    | exact superpose eq491 eq522
    | exact resolve eq522 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq527 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq523 X0 X1
       have i₂ := eq476 X0 X0 X0
       grind)
    | (have i₁ := eq523 X0 X1
       have i₂ := eq476 X0 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq476 eq523
    | exact resolve eq523 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq530 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq527 X0 X1
       have i₂ := eq468 X0 X0
       grind)
    | (have i₁ := eq527 X0 X1
       have i₂ := eq468 X0 (M.op (M.op (M.op X0 X0) X0) X0)
       grind)
    | exact superpose eq468 eq527
    | exact resolve eq527 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq531 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq530 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq530 X0 X1
       have i₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact superpose eq14 eq530
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq530 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 X2 : G, (M.op (M.op X2 X0) (M.op X2 X0)) = (M.op (M.op X2 X0) (M.op (M.op X2 X2) X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq530 (M.op X2 X0) (M.op X2 x)
       have i₂ := eq440 x X2 X0
       grind)
    | exact superpose eq440 eq530
    | exact resolve eq530 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq530 (M.op (M.op X0 X0) X1) X1
       have i₂ := eq468 X1 X0
       grind)
    | exact superpose eq468 eq530
    | exact resolve eq530 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq531 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq546 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = (M.op (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq534 X0 X1
       have i₂ := eq440 X1 (M.op X0 X0) X1
       grind)
    | exact superpose eq440 eq534
    | exact resolve eq534 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq547 : ∀ X0 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X2 X0) (M.op (M.op X2 X2) X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq533 X0 X2
       have i₂ := eq440 X0 X2 X0
       grind)
    | exact superpose eq440 eq533
    | exact resolve eq533 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq548 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (M.op (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 X1
       have i₂ := eq440 X0 X0 X0
       grind)
    | exact superpose eq440 eq546
    | exact resolve eq546 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq551 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq543 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq543
    | (have j0 := eq543 (σ X0) (σ X1)
       grind)
    | exact resolve eq543 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq543 X0 (τ X1)
       grind)
    | exact superpose eq543 eq19
    | (have j1 := eq543 X0 (τ X1)
       grind)
    | exact resolve eq19 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq572 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq543 (σ X0) X1
       grind)
    | exact superpose eq543 eq28
    | (have j1 := eq543 (σ X0) X1
       grind)
    | exact resolve eq28 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq543
  have eq602 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0) X2)) = (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq493 (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0) X2) X1 X3
       have i₂ := eq491 (M.op X1 X1) X0 X2
       grind)
    | exact superpose eq491 eq493
    | exact resolve eq493 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq604 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op (M.op (M.op X2 X2) (M.op X2 X2)) X0) (M.op (M.op X2 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq493 X0 X2 (M.op (M.op X2 X2) X1)
       have i₂ := eq440 X1 (M.op X2 X2) X0
       grind)
    | exact superpose eq440 eq493
    | exact resolve eq493 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq619 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op (M.op (M.op X2 X2) X2) X0) (M.op (M.op X2 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq604 X0 X1 X2
       have i₂ := eq440 X2 X2 X2
       grind)
    | exact superpose eq440 eq604
    | exact resolve eq604 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq620 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X1 (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq602 X0 X1 X2 x
       have i₂ := eq468 x (M.op X1 X1)
       grind)
    | (have i₁ := eq602 X0 X1 X2 x
       have i₂ := eq468 X0 (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) x) x)
       grind)
    | exact superpose eq468 eq602
    | exact resolve eq602 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq626 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X1 (M.op (M.op (M.op (M.op X1 X1) X1) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq620 X0 X1 X2
       have i₂ := eq440 X1 X1 X1
       grind)
    | exact superpose eq440 eq620
    | exact resolve eq620 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq697 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X0) (M.op X2 X0)) (M.op X2 X1)) = (M.op (M.op (M.op X2 X2) X0) (M.op (M.op (M.op X2 X0) (M.op X2 X0)) (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq547 (M.op X2 X1) (M.op X2 X0)
       have i₂ := eq440 X1 X2 X0
       grind)
    | exact superpose eq440 eq547
    | exact resolve eq547 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq547 (M.op (M.op X0 X0) X1) (M.op X0 X1)
       have i₂ := eq547 X1 X0
       grind)
    | exact superpose eq547 eq547
    | exact resolve eq547 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq725 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1)) = (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq698 x X0
       have i₂ := eq476 X0 x (M.op x X0)
       grind)
    | (have i₁ := eq698 x x
       have i₂ := eq476 (M.op x x) x (M.op (M.op x x) x)
       grind)
    | exact superpose eq476 eq698
    | exact resolve eq698 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq726 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X2) X0) (M.op X2 X1)) = (M.op (M.op (M.op X2 X2) X0) (M.op (M.op (M.op X2 X2) X0) (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq697 X0 X1 X1
       have i₂ := eq440 X0 X1 X0
       grind)
    | exact superpose eq440 eq697
    | exact resolve eq697 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq734 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1)) = (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq725 X0 X1
       have i₂ := eq530 (M.op (M.op X0 X0) X1) (M.op X0 X1)
       grind)
    | exact superpose eq530 eq725
    | exact resolve eq725 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq735 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X2) X0) (M.op X2 X1)) = (M.op (M.op (M.op X2 X2) X0) (M.op (M.op X2 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq726 X0 X1 X2
       have i₂ := eq530 (M.op (M.op X2 X2) X0) (M.op X2 X1)
       grind)
    | exact superpose eq530 eq726
    | exact resolve eq726 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq741 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1)) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq734 X0 X1
       have i₂ := eq440 X1 (M.op X0 X0) X1
       grind)
    | exact superpose eq440 eq734
    | exact resolve eq734 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq742 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X2) X0) (M.op X2 X1)) = (M.op (M.op (M.op X2 X2) (M.op X2 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq735 X0 X1 X2
       have i₂ := eq440 X0 (M.op X2 X2) X0
       grind)
    | exact superpose eq440 eq735
    | exact resolve eq735 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq744 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq741 X0 X1
       have i₂ := eq440 X0 X0 X0
       grind)
    | exact superpose eq440 eq741
    | exact resolve eq741 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq745 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X2) X0) (M.op X2 X1)) = (M.op (M.op (M.op X2 X2) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq742 X0 X1 X2
       have i₂ := eq440 X2 X2 X2
       grind)
    | exact superpose eq440 eq742
    | exact resolve eq742 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq754 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X2) X2) (M.op (M.op (M.op (M.op (M.op X2 X2) (M.op X2 X2)) (M.op X2 X2)) X1) X0)) = (M.op (M.op (M.op X2 X2) (M.op X2 X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq548 X2 (M.op (M.op (M.op (M.op (M.op X2 X2) (M.op X2 X2)) (M.op X2 X2)) X1) X0)
       have i₂ := eq626 X1 (M.op X2 X2) X0
       grind)
    | exact superpose eq626 eq548
    | exact resolve eq548 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq493 X0 X0 X1
       have i₂ := eq548 X0 X1
       grind)
    | (have i₁ := eq493 X1 X0 X0
       have i₂ := eq548 X0 X1
       grind)
    | exact superpose eq548 eq493
    | exact resolve eq493 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq765 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq493 X1 X0 X0
       have i₂ := eq548 X0 X1
       grind)
    | (have i₁ := eq493 X0 X0 X1
       have i₂ := eq548 X0 X1
       grind)
    | exact superpose eq548 eq493
    | exact resolve eq493 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq784 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X2) X2) (M.op (M.op (M.op (M.op (M.op X2 X2) (M.op X2 X2)) (M.op X2 X2)) X1) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq754 X0 X1 X2
       have i₂ := eq9 X2 X2 X2
       grind)
    | exact superpose eq9 eq754
    | exact resolve eq754 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq798 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X2) X2) (M.op (M.op (M.op (M.op (M.op X2 X2) (M.op X2 X2)) X1) X2) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq784 X0 X1 X2
       have i₂ := eq488 X2 X2 (M.op X2 X2) X1
       grind)
    | exact superpose eq488 eq784
    | exact resolve eq784 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq801 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X2) X2) (M.op (M.op (M.op (M.op (M.op X2 X2) X2) X1) X2) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq798 X0 X1 X2
       have i₂ := eq440 X2 X2 X2
       grind)
    | exact superpose eq440 eq798
    | exact resolve eq798 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq802 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X2) X2) (M.op (M.op X2 X1) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq801 X0 X1 X2
       have i₂ := eq765 X2 X1
       grind)
    | exact superpose eq765 eq801
    | exact resolve eq801 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq811 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op (M.op (M.op X2 X2) (M.op X2 X2)) X2) (M.op (M.op (M.op (M.op (M.op X2 X2) (M.op X2 X2)) (M.op X2 X2)) X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq757 X2 (M.op (M.op (M.op (M.op (M.op X2 X2) (M.op X2 X2)) (M.op X2 X2)) X1) X0)
       have i₂ := eq626 X1 (M.op X2 X2) X0
       grind)
    | exact superpose eq626 eq757
    | exact resolve eq757 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq819 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op (M.op X0 X0) X1) X0)) = (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq530 (M.op (M.op (M.op X0 X0) X1) X0) X1
       have i₂ := eq757 X0 X1
       grind)
    | exact superpose eq757 eq530
    | exact resolve eq530 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq820 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) = (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq819 X0 X1
       have i₂ := eq440 X0 (M.op (M.op X0 X0) X1) X0
       grind)
    | exact superpose eq440 eq819
    | exact resolve eq819 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq825 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op (M.op (M.op X2 X2) (M.op X2 X2)) X2) (M.op (M.op (M.op (M.op (M.op X2 X2) (M.op X2 X2)) X1) X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq811 X0 X1 X2
       have i₂ := eq488 X2 X2 (M.op X2 X2) X1
       grind)
    | exact superpose eq488 eq811
    | exact resolve eq811 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488 eq811
  have eq830 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) X1) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq820 X0 X1
       have i₂ := eq509 X0 X1 (M.op (M.op X0 X0) X1)
       grind)
    | (have i₁ := eq820 x x
       have i₂ := eq509 x (M.op (M.op x x) x) x
       grind)
    | exact superpose eq509 eq820
    | exact resolve eq820 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509 eq820
  have eq835 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op (M.op (M.op X2 X2) X2) X2) (M.op (M.op (M.op (M.op (M.op X2 X2) X2) X1) X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq825 X0 X1 X0
       have i₂ := eq440 X0 X0 X0
       grind)
    | exact superpose eq440 eq825
    | exact resolve eq825 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq838 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq830 X0 X1
       have i₂ := eq619 X1 X1 X0
       grind)
    | exact superpose eq619 eq830
    | exact resolve eq830 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619 eq830
  have eq843 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op (M.op (M.op X2 X2) X2) X2) (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq835 X0 X1 X2
       have i₂ := eq765 X2 X1
       grind)
    | exact superpose eq765 eq835
    | exact resolve eq835 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq844 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X2 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq843 X0 X1 X2
       have i₂ := eq468 X2 X2
       grind)
    | (have i₁ := eq843 X0 X1 X2
       have i₂ := eq468 X0 (M.op (M.op (M.op X2 X2) X2) X2)
       grind)
    | exact superpose eq468 eq843
    | exact resolve eq843 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq1052 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X0) X0)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq757 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq802 X0 X0 X0
       grind)
    | exact superpose eq802 eq757
    | exact resolve eq757 eq802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq1073 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1052 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq548 X0 X1
       grind)
    | (have i₁ := eq1052 (M.op (M.op X0 X0) X1) X0
       have i₂ := eq548 X0 X1
       grind)
    | exact superpose eq548 eq1052
    | exact resolve eq1052 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1075 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op (M.op (M.op X2 X2) X0) (M.op (M.op (M.op X2 X0) (M.op X2 X0)) (M.op X2 X0))) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1052 (M.op X2 X0) (M.op X2 X1)
       have i₂ := eq440 X1 X2 X0
       grind)
    | exact superpose eq440 eq1052
    | exact resolve eq1052 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1090 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq844 X1 (M.op (M.op X0 X0) X0) (M.op X0 X1)
       have i₂ := eq1052 X0 X1
       grind)
    | exact superpose eq1052 eq844
    | exact resolve eq844 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052
  have eq1103 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1090 X0 X1
       have i₂ := eq440 X1 X0 X1
       grind)
    | exact superpose eq440 eq1090
    | exact resolve eq1090 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1114 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op (M.op (M.op X2 X2) X0) (M.op (M.op (M.op X2 X2) X0) (M.op X2 X0))) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1075 X0 X1 X2
       have i₂ := eq440 X0 X2 X0
       grind)
    | exact superpose eq440 eq1075
    | exact resolve eq1075 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq1116 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1073 X0 X1
       have i₂ := eq493 X0 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq493 eq1073
    | exact resolve eq1073 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq1133 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op (M.op (M.op X2 X2) X0) (M.op (M.op X2 X2) X0)) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1114 X0 X1 X2
       have i₂ := eq530 (M.op (M.op X2 X2) X0) (M.op X2 X0)
       grind)
    | exact superpose eq530 eq1114
    | exact resolve eq1114 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq1135 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1116 X0 X1
       have i₂ := eq838 X0 X1
       grind)
    | exact superpose eq838 eq1116
    | exact resolve eq1116 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838 eq1116
  have eq1143 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op (M.op (M.op X2 X2) (M.op X2 X2)) X0) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1133 X0 X1 X2
       have i₂ := eq440 X0 (M.op X2 X2) X0
       grind)
    | exact superpose eq440 eq1133
    | exact resolve eq1133 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq1145 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op (M.op (M.op X2 X2) X2) X0) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1143 X0 X1 X2
       have i₂ := eq440 X2 X2 X2
       grind)
    | exact superpose eq440 eq1143
    | exact resolve eq1143 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq1150 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) X2) = (M.op (M.op (M.op X1 X0) X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1103 (M.op X1 X0) X2
       have i₂ := eq440 X0 X1 X0
       grind)
    | exact superpose eq440 eq1103
    | exact resolve eq1103 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1157 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq468 X1 X0
       have i₂ := eq1103 X0 X1
       grind)
    | (have i₁ := eq468 X1 X1
       have i₂ := eq1103 X1 X1
       grind)
    | exact superpose eq1103 eq468
    | exact resolve eq468 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1159 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq493 X1 X0 X2
       have i₂ := eq1103 X0 X1
       grind)
    | (have i₁ := eq493 X1 X1 X2
       have i₂ := eq1103 X1 X1
       grind)
    | exact superpose eq1103 eq493
    | exact resolve eq493 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1162 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X0) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq757 X0 X1
       have i₂ := eq1103 X0 X1
       grind)
    | (have i₁ := eq757 X1 X1
       have i₂ := eq1103 X1 X1
       grind)
    | exact superpose eq1103 eq757
    | exact resolve eq757 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq1261 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X1 X0)) = (M.op (M.op (M.op X1 X0) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1135 (M.op X1 X0) X2
       have i₂ := eq440 X0 X1 X0
       grind)
    | exact superpose eq440 eq1135
    | exact resolve eq1135 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1264 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X2) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1135 X0 X1
       have i₂ := eq1135 X0 X2
       grind)
    | (have i₁ := eq1135 X1 X1
       have i₂ := eq1135 X1 X1
       grind)
    | exact superpose eq1135 eq1135
    | exact resolve eq1135 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1269 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq496 X0 X2
       have i₂ := eq1135 X0 X1
       grind)
    | (have i₁ := eq496 X1 X1
       have i₂ := eq1135 X1 X1
       grind)
    | exact superpose eq1135 eq496
    | exact resolve eq496 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq1270 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) X0) = (M.op (M.op (M.op X0 X1) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq548 X0 X2
       have i₂ := eq1135 X0 X1
       grind)
    | (have i₁ := eq548 X1 X1
       have i₂ := eq1135 X1 X1
       grind)
    | exact superpose eq1135 eq548
    | exact resolve eq548 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq1272 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq765 X0 X2
       have i₂ := eq1135 X0 X1
       grind)
    | (have i₁ := eq765 X1 X1
       have i₂ := eq1135 X1 X1
       grind)
    | exact superpose eq1135 eq765
    | exact resolve eq765 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq1276 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq468 X0 X0
       have i₂ := eq1135 X0 X1
       grind)
    | (have i₁ := eq468 X1 X1
       have i₂ := eq1135 X1 X1
       grind)
    | exact superpose eq1135 eq468
    | exact resolve eq468 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1278 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq493 X0 X0 X2
       have i₂ := eq1135 X0 X1
       grind)
    | (have i₁ := eq493 X1 X1 X2
       have i₂ := eq1135 X1 X1
       grind)
    | exact superpose eq1135 eq493
    | exact resolve eq493 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq1282 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0
       have i₂ := eq1135 (σ X0) X1
       grind)
    | (have i₁ := eq57 X0
       have i₂ := eq1135 (σ X0) (σ X0)
       grind)
    | exact superpose eq1135 eq57
    | exact resolve eq57 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq1294 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq440 X1 (M.op X0 X1) X2
       have i₂ := eq1135 X0 X1
       grind)
    | (have i₁ := eq440 X0 (M.op X0 X0) X2
       have i₂ := eq1135 X0 X1
       grind)
    | exact superpose eq1135 eq440
    | exact resolve eq440 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq1303 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) X2) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1294 X0 X1 X2
       have i₂ := eq440 X1 X0 X1
       grind)
    | exact superpose eq440 eq1294
    | exact resolve eq1294 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294
  have eq1311 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X1) X0) = (M.op (M.op (M.op X1 X0) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1261 X0 X1 X2
       have i₂ := eq745 X0 X0 X1
       grind)
    | exact superpose eq745 eq1261
    | exact resolve eq1261 eq745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745 eq1261
  have eq1433 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) X3) X3) = (M.op (M.op (M.op X1 X2) X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1264 (M.op X1 X0) X0 X3
       have i₂ := eq1264 X1 X2 X0
       grind)
    | (have i₁ := eq1264 (M.op X1 X0) X0 X3
       have i₂ := eq1264 X1 X0 X2
       grind)
    | exact superpose eq1264 eq1264
    | exact resolve eq1264 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1507 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X1 X2)) X3) = (M.op (M.op (M.op X1 X2) X3) (M.op (M.op X1 X0) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq440 X2 (M.op X1 X2) X3
       have i₂ := eq1264 X1 X0 X2
       grind)
    | (have i₁ := eq440 X2 (M.op X1 X2) X3
       have i₂ := eq1264 X1 X2 X0
       grind)
    | exact superpose eq1264 eq440
    | exact resolve eq440 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1516 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X2) X3) = (M.op (M.op (M.op X1 X2) X3) (M.op (M.op X1 X0) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1507 X0 X1 X2 X3
       have i₂ := eq440 X2 X1 X2
       grind)
    | exact superpose eq440 eq1507
    | exact resolve eq1507 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1507
  have eq1601 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1269 (M.op (M.op X0 X1) X1) X2 X0
       have i₂ := eq1276 X0 X1
       grind)
    | exact superpose eq1276 eq1269
    | exact resolve eq1269 eq1276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1958 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X2) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1162 X0 X1
       have i₂ := eq1264 (M.op X0 X1) X2 X0
       grind)
    | (have i₁ := eq1162 X0 X1
       have i₂ := eq1264 (M.op X0 X1) X0 X2
       grind)
    | exact superpose eq1264 eq1162
    | exact resolve eq1162 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq2084 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op (M.op (M.op X0 X0) X2) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1272 (M.op (M.op X0 X1) X1) X0 X2
       have i₂ := eq1276 X0 X1
       grind)
    | exact superpose eq1276 eq1272
    | exact resolve eq1272 eq1276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2099 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X1) X3) = (M.op (M.op (M.op X1 X2) X3) (M.op (M.op X1 X2) X1)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq1272 (M.op (M.op X1 X2) X1) x X3
       have i₂ := eq1159 X1 X2 x
       grind)
    | exact superpose eq1159 eq1272
    | exact resolve eq1272 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159
  have eq2127 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X1) = (M.op (M.op (M.op (M.op (M.op X1 X2) X2) X0) X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1264 (M.op (M.op (M.op X1 X2) X2) X0) X3 X1
       have i₂ := eq1272 X1 X2 X0
       grind)
    | exact superpose eq1272 eq1264
    | exact resolve eq1264 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272
  have eq2152 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X1 X2)) X3) = (M.op (M.op (M.op X1 X2) X1) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq2099 X1 X2 X3
       have i₂ := eq440 X1 (M.op X1 X2) X3
       grind)
    | exact superpose eq440 eq2099
    | exact resolve eq2099 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2099
  have eq2155 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) X2) = (M.op (M.op (M.op X0 X1) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2084 X0 X1 X2
       have i₂ := eq1516 X1 X0 X0 X2
       grind)
    | exact superpose eq1516 eq2084
    | exact resolve eq2084 eq1516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084
  have eq2185 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X2) X3) = (M.op (M.op (M.op X1 X2) X1) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq2152 X1 X2 X3
       have i₂ := eq440 X2 X1 X2
       grind)
    | exact superpose eq440 eq2152
    | exact resolve eq2152 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2152
  have eq2873 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op X1 X2) X2) X0) X0) X1) = (k (M.op (M.op (M.op (M.op X1 X2) X2) X0) X0) X1) := by
    intro X0 X1 X2
    grind
  have eq2881 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X2) X2) X0) X0) X3) = (M.op (M.op X1 X3) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1103 X1 X3
       have i₂ := eq1278 X1 X2 X0
       grind)
    | exact superpose eq1278 eq1103
    | exact resolve eq1103 eq1278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq2911 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X2) X0) X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1264 (M.op (M.op (M.op X1 X2) X2) X0) X3 X0
       have i₂ := eq1278 X1 X2 X0
       grind)
    | exact superpose eq1278 eq1264
    | exact resolve eq1264 eq1278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2938 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (k (M.op (M.op (M.op (M.op X1 X2) X2) X0) X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2873 X0 X1 X2
       have i₂ := eq1601 X1 X2 X0
       grind)
    | exact superpose eq1601 eq2873
    | exact resolve eq2873 eq1601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601 eq2873
  have eq3525 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X0) X2) X3) X3) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq468 X3 X1
       have i₂ := eq1958 X1 X2 X0
       grind)
    | exact superpose eq1958 eq468
    | exact resolve eq468 eq1958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4431 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1264 (M.op (M.op (M.op X0 X0) X0) X1) X3 (M.op X0 X2)
       have i₂ := eq1145 X1 X2 X0
       grind)
    | exact superpose eq1145 eq1264
    | exact resolve eq1264 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145 eq1264
  have eq4455 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4431 X0 X1 X2 x
       have i₂ := eq2127 X1 X0 X0 x
       grind)
    | exact superpose eq2127 eq4431
    | exact resolve eq4431 eq2127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2127 eq4431
  have eq5270 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X2) X0) = (M.op (M.op (M.op X1 X3) X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1270 X1 X3 X0
       have i₂ := eq1270 X1 X2 X0
       grind)
    | (have i₁ := eq1270 X2 X1 X2
       have i₂ := eq1270 X2 X2 X2
       grind)
    | exact superpose eq1270 eq1270
    | exact resolve eq1270 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270
  have eq5938 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X2) X2) (M.op (M.op X2 X2) X2)) = (M.op (M.op (M.op (M.op (M.op (M.op X2 X1) X0) X0) X3) X3) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1958 (M.op (M.op X2 X2) X2) X1 X3
       have i₂ := eq1311 X1 X2 X0
       grind)
    | (have i₁ := eq1958 (M.op (M.op X1 X0) X2) X2 X2
       have i₂ := eq1311 X0 X1 X2
       grind)
    | exact superpose eq1311 eq1958
    | exact resolve eq1958 eq1311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6022 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X2) X2) X2) = (M.op (M.op (M.op (M.op (M.op (M.op X2 X1) X0) X0) X3) X3) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5938 X0 X1 X2 X3
       have i₂ := eq476 X2 X2 X2
       grind)
    | (have i₁ := eq5938 X0 X1 X0 X3
       have i₂ := eq476 X0 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq476 eq5938
    | exact resolve eq5938 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476 eq5938
  have eq6076 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op (M.op X2 X1) X0) X0) X3) X3) X1) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6022 X0 X1 X2 X3
       have i₂ := eq1157 X2 X2
       grind)
    | exact superpose eq1157 eq6022
    | exact resolve eq6022 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157 eq6022
  have eq13580 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op X2 X2) X2) X1) X0) X3) = (M.op (M.op (M.op (M.op (M.op X2 X1) X0) X4) X4) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5270 X3 (M.op (M.op X2 X1) X0) X4 X0
       have i₂ := eq1311 X1 X2 X0
       grind)
    | (have i₁ := eq5270 X0 (M.op (M.op X1 X1) X1) X2 X0
       have i₂ := eq1311 X0 X1 X2
       grind)
    | exact superpose eq1311 eq5270
    | exact resolve eq5270 eq1311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311
  have eq13898 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X3 X2) X2) X0) (M.op (M.op (M.op X3 X1) X1) X4)) = (M.op (M.op (M.op (M.op X3 X2) X2) X0) (M.op (M.op X3 X1) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4455 (M.op (M.op X1 X2) X2) X0 X2
       have i₂ := eq5270 X0 X1 X2 X3
       grind)
    | (have i₁ := eq4455 (M.op (M.op X1 X3) X3) X0 X2
       have i₂ := eq5270 X0 X1 X2 X3
       grind)
    | exact superpose eq5270 eq4455
    | exact resolve eq4455 eq5270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4455 eq5270
  have eq16864 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op (M.op X3 X1) X0) X2) X2) X0) X1) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3525 X0 X3 X1 X1
       have i₂ := eq1433 X0 (M.op (M.op X3 X1) X0) X2 X1
       grind)
    | (have i₁ := eq3525 X2 X1 X2 X0
       have i₂ := eq1433 X0 (M.op (M.op X1 X2) X2) X2 X3
       grind)
    | exact superpose eq1433 eq3525
    | exact resolve eq3525 eq1433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1433 eq3525
  have eq19549 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X2 X3) X0) X0) X1) (M.op (M.op (M.op (M.op X2 X3) X0) X0) X1)) = (M.op (M.op (M.op (M.op (M.op X2 X3) X0) X0) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq844 X3 X1 (M.op (M.op (M.op (M.op X2 X3) X0) X0) X1)
       have i₂ := eq6076 X0 X3 X2 X1
       grind)
    | exact superpose eq6076 eq844
    | exact resolve eq844 eq6076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq6076
  have eq19597 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X2 X3) X0) X0) X1) X2) = (M.op (M.op (M.op (M.op (M.op X2 X3) X0) X0) X1) (M.op (M.op (M.op X2 X3) X0) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19549 X0 X1 X2 X3
       have i₂ := eq13898 X1 X0 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq13898 eq19549
    | exact resolve eq19549 eq13898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13898 eq19549
  have eq19730 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X2 X3) X0) X0) X1) X2) = (M.op (M.op (M.op (M.op (M.op X2 X3) X0) (M.op (M.op X2 X3) X0)) X0) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19597 X0 X1 X2 X3
       have i₂ := eq1150 X0 (M.op (M.op X2 X3) X0) X1
       grind)
    | exact superpose eq1150 eq19597
    | exact resolve eq19597 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19597
  have eq19770 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X2 X3) X0) X0) X1) X2) = (M.op (M.op (M.op (M.op (M.op X2 X3) X0) X0) (M.op (M.op X2 X3) X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19730 X0 X1 X2 X3
       have i₂ := eq2185 (M.op (M.op X2 X3) X0) X0 X1
       grind)
    | exact superpose eq2185 eq19730
    | exact resolve eq19730 eq2185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2185 eq19730
  have eq19786 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X2 X3) X0) X0) X1) X2) = (M.op (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X3)) X0) X0) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19770 X0 X1 X2 X3
       have i₂ := eq1150 X0 (M.op X2 X3) X0
       grind)
    | exact superpose eq1150 eq19770
    | exact resolve eq19770 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19770
  have eq19799 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X1) = (M.op (M.op (M.op (M.op (M.op X2 X3) X0) X0) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19786 X0 X1 X2 X3
       have i₂ := eq468 X0 (M.op X2 X3)
       grind)
    | (have i₁ := eq19786 X0 X1 X2 X3
       have i₂ := eq468 X0 (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X3)) X0) X0)
       grind)
    | exact superpose eq468 eq19786
    | exact resolve eq19786 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19786
  have eq28707 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq565 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq565
    | exact resolve eq565 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq28773 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28707 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq28707
    | (have j0 := eq28707 X0 X1
       grind)
    | exact resolve eq28707 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28707
  have eq28848 : ∀ X0 X1 : G, (k (τ (M.op X0 X0)) (τ X0)) = (τ (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1282 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1282
    | exact resolve eq1282 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282
  have eq28920 : ∀ X0 X1 : G, (τ (k (M.op X0 X0) X0)) = (τ (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28848 X0 X1
       have i₂ := eq30 X0 (M.op X0 X0)
       grind)
    | exact superpose eq30 eq28848
    | exact resolve eq28848 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28848
  have eq28929 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) X0)) = (τ (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    grind
  clear eq28920
  have eq28945 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X1) X1)) = (τ (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28929 X0 X2
       have i₂ := eq28929 X0 X1
       grind)
    | (have i₁ := eq28929 X1 X1
       have i₂ := eq28929 X1 X1
       grind)
    | exact superpose eq28929 eq28929
    | exact resolve eq28929 eq28929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28979 : ∀ X0 X1 X2 : G, (k (τ X2) (τ (M.op (M.op X0 X0) X0))) = (τ (k X2 (M.op (M.op X0 X1) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 (M.op (M.op X0 X1) X1) X2
       have i₂ := eq28929 X0 X1
       grind)
    | (have i₁ := eq30 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq28929 X0 X1
       grind)
    | exact superpose eq28929 eq30
    | exact resolve eq30 eq28929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28929
  have eq28987 : ∀ X0 X1 X2 : G, (τ (k X2 (M.op (M.op X0 X0) X0))) = (τ (k X2 (M.op (M.op X0 X1) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28979 X0 X1 X2
       have i₂ := eq30 (M.op (M.op X0 X0) X0) X2
       grind)
    | exact superpose eq30 eq28979
    | exact resolve eq28979 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28979
  have eq33584 : ∀ X0 X1 : G, (τ X0) = (k X1 (τ (M.op (M.op X0 X0) (σ X1)))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq572 X0 (M.op (M.op x x) (σ X0))
       have i₂ := eq468 (σ X0) x
       grind)
    | exact superpose eq468 eq572
    | exact resolve eq572 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq33699 : ∀ X0 X1 : G, (τ X1) = (k (τ X0) (τ (M.op (M.op X1 X1) X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33584 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33584
    | exact resolve eq33584 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33584
  have eq33725 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 (M.op (M.op X1 X1) X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33699 X0 X1
       have i₂ := eq30 (M.op (M.op X1 X1) X0) X0
       grind)
    | exact superpose eq30 eq33699
    | (have j0 := eq33699 (τ X1) (τ (k X0 (M.op (M.op X1 X1) X0)))
       grind)
    | exact resolve eq33699 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33699
  have eq33762 : ∀ X0 X1 : G, (σ (τ X1)) = (k X0 (M.op (M.op X1 X1) X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 (M.op (M.op X1 X1) X0))
       have i₂ := eq33725 X0 X1
       grind)
    | exact superpose eq33725 eq11
    | (have j1 := eq33725 (σ (τ X1)) (k X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact resolve eq11 eq33725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33725
  have eq33776 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X1) X0)) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33762 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq33762
    | (have j0 := eq33762 (k X0 (M.op (M.op X1 X1) X0)) X1
       grind)
    | exact resolve eq33762 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33762
  have eq33809 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (k X2 (M.op (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X0) X0)) X2)) ∨ (M.op (M.op X0 X0) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33776 X2 (M.op (M.op X0 X0) X0)
       have i₂ := eq2155 X0 X1 (M.op (M.op X0 X0) X0)
       grind)
    | (have i₁ := eq33776 X0 (M.op (M.op X0 X1) X1)
       have i₂ := eq2155 X0 X1 (M.op (M.op X0 X1) X1)
       grind)
    | exact superpose eq2155 eq33776
    | (have j0 := eq33776 (M.op (M.op X0 X0) X0) (k X2 (M.op (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X0) X0)) X2))
       grind)
    | exact resolve eq33776 eq2155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2155 eq33776
  have eq33857 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (k X2 (M.op (M.op (M.op (M.op X0 X0) X1) X1) X2)) ∨ (M.op (M.op X0 X0) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33809 X0 X1 X2
       have i₂ := eq1303 X0 X1 X1
       grind)
    | exact superpose eq1303 eq33809
    | (have j0 := eq33809 X0 X1 (k X2 (M.op (M.op (M.op (M.op X0 X0) X1) X1) X2))
       grind)
    | exact resolve eq33809 eq1303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1303 eq33809
  have eq33864 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X0) = (k X2 (M.op X0 X2)) ∨ (M.op (M.op X0 X0) X0) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq33857 X0 x X2
       have i₂ := eq468 x X0
       grind)
    | (have i₁ := eq33857 X0 x X2
       have i₂ := eq468 X0 (M.op (M.op (M.op X0 X0) x) x)
       grind)
    | exact superpose eq468 eq33857
    | (have j0 := eq33857 X0 x (k X2 (M.op X0 X2))
       grind)
    | exact resolve eq33857 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33857
  have eq59066 : ∀ X1 X2 X3 : G, (M.op X1 X1) = (k (M.op (M.op (M.op X1 X1) X3) X3) (M.op (M.op X1 X2) X2)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq2938 x (M.op (M.op x X1) X1) X2
       have i₂ := eq1278 x X1 X2
       grind)
    | exact superpose eq1278 eq2938
    | exact resolve eq2938 eq1278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278 eq2938
  have eq59257 : ∀ X1 X2 : G, (M.op X1 X1) = (k X1 (M.op (M.op X1 X2) X2)) := by
    intro X1 X2
    first
    | (have i₁ := eq59066 X1 X2 x
       have i₂ := eq468 x X1
       grind)
    | (have i₁ := eq59066 X1 X2 x
       have i₂ := eq468 x (M.op (M.op (M.op X1 X1) x) x)
       grind)
    | exact superpose eq468 eq59066
    | exact resolve eq59066 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59066
  have eq101704 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X2) X2)) = (σ (τ (k X0 (M.op (M.op X1 X1) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X0 (M.op (M.op X1 X2) X2))
       have i₂ := eq28987 X1 X2 X0
       grind)
    | (have i₁ := eq11 (k X2 (M.op (M.op X0 X0) X0))
       have i₂ := eq28987 X0 X1 X2
       grind)
    | exact superpose eq28987 eq11
    | exact resolve eq11 eq28987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28987
  have eq101727 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X2) X2)) = (k X0 (M.op (M.op X1 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq101704 X0 X1 X2
       have i₂ := eq11 (k X0 (M.op (M.op X1 X1) X1))
       grind)
    | exact superpose eq11 eq101704
    | exact resolve eq101704 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101704
  have eq101886 : ∀ X0 X2 X3 X4 : G, (k X4 (M.op (M.op X3 X3) X0)) = (k X4 (M.op (M.op (M.op (M.op (M.op X3 X2) X2) X0) (M.op (M.op (M.op X3 X2) X2) X0)) (M.op (M.op (M.op X3 X2) X2) X0))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq101727 X4 (M.op (M.op (M.op X3 X2) X2) X0) x
       have i₂ := eq2911 X0 X3 X2 x
       grind)
    | exact superpose eq2911 eq101727
    | exact resolve eq101727 eq2911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2911 eq101727
  have eq102048 : ∀ X0 X2 X3 X4 : G, (k X4 (M.op (M.op X3 X3) X0)) = (k X4 (M.op (M.op (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X3 X2) X2)) X0) (M.op (M.op (M.op X3 X2) X2) X0))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq101886 X0 X2 X3 X4
       have i₂ := eq1150 X0 (M.op (M.op X3 X2) X2) (M.op (M.op (M.op X3 X2) X2) X0)
       grind)
    | exact superpose eq1150 eq101886
    | exact resolve eq101886 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150 eq101886
  have eq102146 : ∀ X0 X2 X3 X4 : G, (k X4 (M.op (M.op X3 X3) X0)) = (k X4 (M.op (M.op (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2)) X0)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq102048 X0 X2 X3 X4
       have i₂ := eq744 (M.op (M.op X3 X2) X2) X0
       grind)
    | exact superpose eq744 eq102048
    | exact resolve eq102048 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744 eq102048
  have eq102231 : ∀ X0 X2 X3 X4 : G, (k X4 (M.op (M.op X3 X3) X0)) = (k X4 (M.op (M.op (M.op (M.op (M.op X3 X3) X3) X2) X2) X0)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq102146 X0 X2 X3 X4
       have i₂ := eq13580 X2 X2 X3 X0 (M.op (M.op X3 X2) X2)
       grind)
    | (have i₁ := eq102146 X3 X2 X2 X4
       have i₂ := eq13580 (M.op (M.op X2 X2) X2) (M.op (M.op X2 X2) X2) X2 X3 X4
       grind)
    | exact superpose eq13580 eq102146
    | exact resolve eq102146 eq13580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13580 eq102146
  have eq102296 : ∀ X0 X3 X4 : G, (k X4 (M.op (M.op X3 X0) X3)) = (k X4 (M.op (M.op X3 X3) X0)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq102231 X0 x X3 X4
       have i₂ := eq2881 x X3 X3 X0
       grind)
    | exact superpose eq2881 eq102231
    | exact resolve eq102231 eq2881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2881 eq102231
  have eq207636 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq551 y x
       grind)
    | exact superpose eq551 eq16
    | (have j1 := eq551 y x
       grind)
    | exact resolve eq16 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq208834 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq207636
       have i₂ := eq28773 x y
       grind)
    | exact superpose eq28773 eq207636
    | (have j1 := eq28773 (σ x) (σ y)
       grind)
    | (have r₁ := eq207636
       have r₂ := eq28773 x y
       grind)
    | exact resolve eq207636 eq28773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28773 eq207636
  have eq208835 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq208834
  have eq208975 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (M.op (M.op (σ y) X0) X1) X1) X0) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16864 X0 (σ y) X1 (σ x)
       have i₂ := eq208835
       grind)
    | exact superpose eq208835 eq16864
    | exact resolve eq16864 eq208835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208835
  have eq209176 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq208975 X0 x
       have i₂ := eq19799 x X0 (σ y) X0
       grind)
    | exact superpose eq19799 eq208975
    | exact resolve eq208975 eq19799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208975
  have eq211350 : ∀ X1 : G, (τ (σ x)) = (τ (M.op (M.op (σ y) X1) X1)) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq28945 (σ y) x X1
       have i₂ := eq209176 x
       grind)
    | exact superpose eq209176 eq28945
    | exact resolve eq28945 eq209176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28945 eq209176
  have eq211737 : ∀ X1 : G, x = (τ (M.op (M.op (σ y) X1) X1)) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq211350 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq211350
    | exact resolve eq211350 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211350
  have eq268147 : ∀ X0 X1 : G, (M.op (k X0 (M.op X1 X0)) X1) = X1 ∨ (M.op (M.op X1 X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1276 X1 X1
       have i₂ := eq33864 X1 X0
       grind)
    | exact superpose eq33864 eq1276
    | (have j1 := eq33864 X1 X0
       grind)
    | exact resolve eq1276 eq33864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33864
  have eq272847 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = X1 ∨ (M.op (k X0 (M.op X1 X0)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1269 X1 X1 X2
       have i₂ := eq268147 X0 X1
       grind)
    | (have i₁ := eq1269 X0 X1 X2
       have i₂ := eq268147 (M.op (M.op X0 X1) X1) X1
       grind)
    | exact superpose eq268147 eq1269
    | (have j1 := eq268147 X0 X1
       grind)
    | exact resolve eq1269 eq268147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268147
  have eq285693 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op X2 X3) X3) (M.op X2 X0)) ∨ (M.op (k X1 (M.op X2 X1)) X2) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1958 X1 (M.op X2 X0) X3
       have i₂ := eq272847 X1 X2 X0
       grind)
    | exact superpose eq272847 eq1958
    | (have j1 := eq272847 X1 X2 X2
       grind)
    | exact resolve eq1958 eq272847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272847
  have eq287023 : ∀ X1 X2 : G, (M.op (k X1 (M.op X2 X1)) X2) = X2 ∨ (M.op X1 X1) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq285693 x X1 X2 x
       have i₂ := eq1269 X2 x x
       grind)
    | exact superpose eq1269 eq285693
    | (have j0 := eq285693 x X1 X2 x
       grind)
    | exact resolve eq285693 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285693
  have eq287653 : ∀ X0 X1 X2 X3 : G, (k X1 (M.op X0 X1)) = (M.op (M.op (M.op (M.op (M.op X0 X2) X3) X3) X2) X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16864 X2 X0 X3 (k X1 (M.op X0 X1))
       have i₂ := eq287023 X1 X0
       grind)
    | exact superpose eq287023 eq16864
    | (have j1 := eq287023 X1 X0
       grind)
    | exact resolve eq16864 eq287023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16864 eq287023
  have eq287869 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X2) = (k X1 (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq287653 X0 X1 X2 x
       have i₂ := eq19799 x X2 X0 X2
       grind)
    | exact superpose eq19799 eq287653
    | (have j0 := eq287653 X0 X1 X2 x
       grind)
    | exact resolve eq287653 eq19799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19799 eq287653
  have eq303038 : ∀ X0 X2 : G, (k X2 (M.op (M.op X0 X0) X2)) = X0 ∨ (M.op X0 X0) = (M.op X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq287869 (M.op X0 X0) X2 x
       have i₂ := eq468 x X0
       grind)
    | exact superpose eq468 eq287869
    | (have j0 := eq287869 (M.op X2 X2) X0 X2
       grind)
    | exact resolve eq287869 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287869
  have eq308476 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X0) X1)) = X1 ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq102296 X0 X1 X0
       have i₂ := eq303038 X1 X0
       grind)
    | exact superpose eq303038 eq102296
    | (have j1 := eq303038 X1 X0
       grind)
    | exact resolve eq102296 eq303038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102296 eq303038
  have eq312742 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq308476 X0 (M.op X1 X0)
       have i₂ := eq1269 X1 X0 X0
       grind)
    | exact superpose eq1269 eq308476
    | (have j0 := eq308476 (M.op X1 X0) X0
       grind)
    | exact resolve eq308476 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269 eq308476
  have eq312926 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X1) X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq312742 X0 X1
       have i₂ := eq440 X0 X1 X0
       grind)
    | exact superpose eq440 eq312742
    | (have j0 := eq312742 X0 X1
       grind)
    | exact resolve eq312742 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440 eq312742
  have eq314430 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1276 X0 X0
       have i₂ := eq312926 X0 X0
       grind)
    | exact superpose eq312926 eq1276
    | (have j1 := eq312926 X0 X0
       grind)
    | exact resolve eq1276 eq312926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312926
  have eq315968 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq59257 X0 X0
       have i₂ := eq314430 X0
       grind)
    | exact superpose eq314430 eq59257
    | (have j1 := eq314430 X0
       grind)
    | exact resolve eq59257 eq314430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59257 eq314430
  have eq316030 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq315968 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315968
  have eq316111 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq316030 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq316030
    | exact resolve eq316030 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq316112 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq316030 (τ X0)
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq316030
    | exact resolve eq316030 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq316255 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq316112 X0
       have i₂ := eq316030 X0
       grind)
    | exact superpose eq316030 eq316112
    | exact resolve eq316112 eq316030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316112
  have eq316256 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq316111 X0
       have i₂ := eq316030 X0
       grind)
    | exact superpose eq316030 eq316111
    | exact resolve eq316111 eq316030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316030 eq316111
  have eq316416 : ∀ X0 : G, (M.op x x) = (τ (M.op (M.op (M.op (σ y) X0) X0) (M.op (M.op (σ y) X0) X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq316255 (M.op (M.op (σ y) x) x)
       have i₂ := eq211737 x
       grind)
    | exact superpose eq211737 eq316255
    | exact resolve eq316255 eq211737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211737 eq316255
  have eq316988 : ∀ X0 : G, (M.op x x) = (τ (M.op (M.op (M.op (σ y) (σ y)) X0) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq316416 X0
       have i₂ := eq1516 X0 (σ y) X0 X0
       grind)
    | exact superpose eq1516 eq316416
    | exact resolve eq316416 eq1516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516 eq316416
  have eq317070 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq316988 x
       have i₂ := eq468 x (σ y)
       grind)
    | (have i₁ := eq316988 x
       have i₂ := eq468 x (M.op (M.op (M.op (σ y) (σ y)) x) x)
       grind)
    | exact superpose eq468 eq316988
    | exact resolve eq316988 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316988
  have eq317121 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq317070
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq317070
    | exact resolve eq317070 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317070
  have eq318118 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq468 X1 (σ X0)
       have i₂ := eq316256 X0
       grind)
    | exact superpose eq316256 eq468
    | exact resolve eq468 eq316256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468 eq316256
  have eq318850 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op y X0) X0) y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1958 x y X0
       have i₂ := eq317121
       grind)
    | exact superpose eq317121 eq1958
    | exact resolve eq1958 eq317121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958 eq317121
  have eq319225 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq318850 x
       have i₂ := eq1276 y x
       grind)
    | exact superpose eq1276 eq318850
    | exact resolve eq318850 eq1276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318850
  have eq319226 : y = (M.op x x) := by grind
  clear eq319225
  have eq319393 : y = (M.op x y) := by
    first
    | (have i₁ := eq530 x x
       have i₂ := eq319226
       grind)
    | exact superpose eq319226 eq530
    | exact resolve eq530 eq319226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq338405 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq318118 x X0
       have i₂ := eq319226
       grind)
    | exact superpose eq319226 eq318118
    | exact resolve eq318118 eq319226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318118 eq319226
  have eq339824 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1276 (σ y) x
       have i₂ := eq338405 x
       grind)
    | exact superpose eq338405 eq1276
    | exact resolve eq1276 eq338405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276 eq338405
  have eq340563 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq339824
       grind)
    | exact superpose eq339824 eq16
    | exact resolve eq16 eq339824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339824
  have eq341041 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq340563
       have i₂ := eq319393
       grind)
    | exact superpose eq319393 eq340563
    | exact resolve eq340563 eq319393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319393 eq340563
  have eq341042 : False := by grind
  exact eq341042

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxy_y_pyx_Equation2666 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq51 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq52 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1) := by
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
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3) := by
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
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq76 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq95 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq37 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq99 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq110 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq99
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq111
    | exact resolve eq111 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq170 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
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
  have eq209 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 y
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ y)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq417 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq247 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq247
    | exact resolve eq247 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq247 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq247
    | (have j0 := eq247 X0 x
       grind)
    | exact resolve eq247 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq499 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) X2)) y) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq500 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) X2)) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq516 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq722 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (σ (k X0 X1)) (M.op (σ X1) X2)) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X1) (σ X0) X2
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq14
    | (have j1 := eq93 X0 X1
       grind)
    | exact resolve eq14 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq931 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) y) := by
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
  have eq932 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq516
    | (have j0 := eq516 (σ x) (σ y) X0
       grind)
    | exact resolve eq516 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq944 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x x) X0) := by
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
  have eq945 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq516
    | (have j0 := eq516 (σ x) X0 (σ y)
       grind)
    | exact resolve eq516 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq950 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
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
  have eq963 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1)) = (k (M.op (M.op X0 X0) X1) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq1021 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq950 X0 (M.op X0 X1)
       have i₂ := eq516 X0 X0 X1
       grind)
    | exact superpose eq516 eq950
    | exact resolve eq950 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1022 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq950 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq950 X0 (M.op X0 X0)
       grind)
    | exact superpose eq950 eq950
    | exact resolve eq950 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1026 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 X1 X1 X0
       have i₂ := eq950 (M.op X0 X1) X0
       grind)
    | exact superpose eq950 eq56
    | exact resolve eq56 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1032 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X1
       have i₂ := eq950 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq950 eq14
    | exact resolve eq14 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1052 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1026 X0 X1
       have i₂ := eq516 X0 X1 X1
       grind)
    | exact superpose eq516 eq1026
    | exact resolve eq1026 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq1170 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq944 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq944
    | (have j0 := eq944 y
       grind)
    | exact resolve eq944 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1222 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1170
       have i₂ := eq931 X0
       grind)
    | exact superpose eq931 eq1170
    | exact resolve eq1170 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1373 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq27 eq945
    | (have j0 := eq945 (σ y)
       grind)
    | exact resolve eq945 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1425 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq932 eq1373
    | exact resolve eq1373 eq932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1548 : (M.op x x) = (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op x x)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1021 (M.op x x) y
       have i₂ := eq1170
       grind)
    | exact superpose eq1170 eq1021
    | exact resolve eq1021 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170
  have eq1552 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq209 eq1021
    | exact resolve eq1021 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1554 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1373 eq1021
    | exact resolve eq1021 eq1373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1558 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq216 eq1021
    | exact resolve eq1021 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1588 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq1558
       have i₂ := eq950 sF4 (M.op sF4 sF4)
       grind)
    | exact superpose eq950 eq1558
    | exact resolve eq1558 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1558
  have eq1592 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1554
       have i₂ := eq950 sF2 (M.op sF2 sF2)
       grind)
    | exact superpose eq950 eq1554
    | exact resolve eq1554 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554
  have eq1594 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1552
       have i₂ := eq950 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq950 eq1552
    | exact resolve eq1552 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552
  have eq1598 : (M.op x x) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1548
       have i₂ := eq950 x (M.op x x)
       grind)
    | exact superpose eq950 eq1548
    | exact resolve eq1548 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548
  have eq1677 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1588 eq216
    | exact resolve eq216 eq1588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1687 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1588 eq516
    | exact resolve eq516 eq1588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1693 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (k (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by grind
  have eq1695 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq1687 x
       have i₂ := eq516 sF4 sF2 x
       grind)
    | exact superpose eq516 eq1687
    | exact resolve eq1687 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1687
  have eq1699 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq1588 eq1695
    | exact resolve eq1695 eq1588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695
  have eq1708 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq1594 eq209
    | exact resolve eq209 eq1594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1718 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1594 eq516
    | exact resolve eq516 eq1594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1726 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq1718 x
       have i₂ := eq516 sF0 x x
       grind)
    | exact superpose eq516 eq1718
    | exact resolve eq1718 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1718
  have eq1730 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq1594 eq1726
    | exact resolve eq1726 eq1594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726
  have eq1880 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq1588 eq1592
    | exact resolve eq1592 eq1588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1592
  have eq1881 : (M.op x x) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq1594 eq1598
    | exact resolve eq1598 eq1594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598
  have eq2478 : ∀ X0 : G, (M.op (M.op (M.op x y) x) X0) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1594 eq1052
    | exact resolve eq1052 eq1594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2480 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1052 (M.op X0 X1) X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq1052
    | exact resolve eq1052 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2482 : x = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | exact superpose eq209 eq1052
    | exact resolve eq1052 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2484 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq216 eq1052
    | exact resolve eq1052 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2488 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1052 (M.op (M.op X0 X0) X0) (M.op X0 X1)
       have i₂ := eq1021 X0 X1
       grind)
    | exact superpose eq1021 eq1052
    | exact resolve eq1052 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2509 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq950 X0 X1
       have i₂ := eq1052 X0 X1
       grind)
    | (have i₁ := eq950 X1 X1
       have i₂ := eq1052 X1 X1
       grind)
    | exact superpose eq1052 eq950
    | exact resolve eq950 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq2572 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2488 X0 X1
       have i₂ := eq1032 X0 X0
       grind)
    | exact superpose eq1032 eq2488
    | exact resolve eq2488 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2488
  have eq2582 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2572 X0 X1
       have i₂ := eq516 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq516 eq2572
    | exact resolve eq2572 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2572
  have eq2587 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2582 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq2582
    | exact resolve eq2582 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2582
  have eq2598 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) y) X0) x) = (M.op (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) X0) := by
    intro X0
    first
    | exact superpose eq2482 eq516
    | exact resolve eq516 eq2482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2601 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) y) X0) x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) y) X0) := by
    intro X0
    first
    | (have i₁ := eq2598 X0
       have i₂ := eq516 sF0 y y
       grind)
    | exact superpose eq516 eq2598
    | exact resolve eq2598 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2598
  have eq2608 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) y) X0) x) := by
    intro X0
    first
    | exact superpose eq209 eq2601
    | exact resolve eq2601 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq2601
  have eq2623 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq2484 eq516
    | exact resolve eq516 eq2484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2624 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) (M.op (M.op (σ x) (σ y)) (σ y))) (σ x)) := by
    first
    | exact superpose eq2484 eq1021
    | exact resolve eq1021 eq2484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq2625 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq2624
       have i₂ := eq516 sF4 sF3 sF3
       grind)
    | exact superpose eq516 eq2624
    | exact resolve eq2624 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2624
  have eq2626 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq2623 X0
       have i₂ := eq516 sF4 sF3 sF3
       grind)
    | exact superpose eq516 eq2623
    | exact resolve eq2623 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2623
  have eq2632 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) (σ x)) := by
    first
    | exact superpose eq216 eq2625
    | exact resolve eq2625 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2625
  have eq2633 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq216 eq2626
    | exact resolve eq2626 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2626
  have eq2637 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq2632
       have i₂ := eq1052 sF2 (M.op sF4 sF3)
       grind)
    | exact superpose eq1052 eq2632
    | exact resolve eq2632 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2632
  have eq2727 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq1222 eq2509
    | exact resolve eq2509 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2766 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq1594 eq2727
    | exact resolve eq2727 eq1594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2727
  have eq2959 : (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq2484 eq2587
    | exact resolve eq2587 eq2484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2963 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq2587 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2587
    | (have j0 := eq2587 x y
       grind)
    | exact resolve eq2587 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2969 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq2587
    | (have j0 := eq2587 (σ x) (σ y)
       grind)
    | exact resolve eq2587 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3025 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq2959
       have i₂ := eq516 sF4 sF3 sF3
       grind)
    | exact superpose eq516 eq2959
    | exact resolve eq2959 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2959
  have eq3061 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq216 eq3025
    | exact resolve eq3025 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3025
  have eq3803 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) y) := by
    intro X1
    first
    | exact superpose eq1222 eq212
    | (have j0 := eq212 y X1
       grind)
    | exact resolve eq212 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq3804 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) y) := by
    intro X1
    first
    | exact superpose eq1594 eq3803
    | exact resolve eq3803 eq1594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3803
  have eq3860 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x (M.op (M.op (M.op x y) x) X0)) X1)) = (M.op (M.op (M.op x (M.op (M.op (M.op x y) x) X0)) (M.op x (M.op (M.op (M.op x y) x) X0))) y) := by
    intro X0 X1
    first
    | exact superpose eq3804 eq516
    | exact resolve eq516 eq3804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3868 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x (M.op (M.op (M.op x y) x) X0)) X1)) = (M.op (M.op (M.op x (M.op (M.op (M.op x y) x) X0)) y) (M.op x (M.op (M.op (M.op x y) x) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3860 X0 X1
       have i₂ := eq1052 (M.op x (M.op (M.op sF0 x) X0)) y
       grind)
    | exact superpose eq1052 eq3860
    | exact resolve eq3860 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3860
  have eq3874 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x (M.op (M.op (M.op x y) x) X0)) X1)) = (M.op (M.op (M.op x y) x) (M.op x (M.op (M.op (M.op x y) x) X0))) := by
    intro X0 X1
    first
    | exact superpose eq3804 eq3868
    | exact resolve eq3868 eq3804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3868
  have eq3901 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2480 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq2480 X0 X1
       grind)
    | exact superpose eq2480 eq2480
    | exact resolve eq2480 eq2480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3907 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq3804 eq2480
    | exact resolve eq2480 eq3804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3804
  have eq3916 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq2482 eq2480
    | exact resolve eq2480 eq2482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2482
  have eq3927 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq2484 eq2480
    | exact resolve eq2480 eq2484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3964 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2587 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq2480 X0 X1
       grind)
    | exact superpose eq2480 eq2587
    | exact resolve eq2587 eq2480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3965 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3964 X0 X1
       have i₂ := eq516 (M.op X0 X1) X1 X1
       grind)
    | exact superpose eq516 eq3964
    | exact resolve eq3964 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3964
  have eq3987 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq3927
       have i₂ := eq1052 sF2 sF4
       grind)
    | exact superpose eq1052 eq3927
    | exact resolve eq3927 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3927
  have eq3996 : (M.op (M.op x y) y) = (M.op (M.op x x) (M.op x y)) := by
    first
    | (have i₁ := eq3916
       have i₂ := eq1052 x sF0
       grind)
    | exact superpose eq1052 eq3916
    | exact resolve eq3916 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3916
  have eq4004 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op x (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq1708 eq3907
    | exact resolve eq3907 eq1708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1708 eq3907
  have eq4008 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3901 X0 X1
       have i₂ := eq1052 X0 (M.op X0 X1)
       grind)
    | exact superpose eq1052 eq3901
    | exact resolve eq3901 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3901
  have eq4022 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3965 X0 X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq3965
    | exact resolve eq3965 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3965
  have eq4036 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq945 eq3987
    | exact resolve eq3987 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq3987
  have eq4041 : (M.op (M.op x y) y) = (M.op (M.op x x) x) := by
    first
    | exact superpose eq944 eq3996
    | exact resolve eq3996 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944 eq3996
  have eq4045 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op (M.op x y) x) X0)) := by
    intro X0
    first
    | exact superpose eq1881 eq4004
    | exact resolve eq4004 eq1881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1881 eq4004
  have eq4047 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4008 X0 X1
       have i₂ := eq516 X0 X0 X1
       grind)
    | exact superpose eq516 eq4008
    | exact resolve eq4008 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4008
  have eq4252 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq4036 eq1032
    | exact resolve eq1032 eq4036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq4488 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1425 eq219
    | (have j0 := eq219 (σ y) X1
       grind)
    | exact resolve eq219 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq4489 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1588 eq4488
    | exact resolve eq4488 eq1588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4488
  have eq4507 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq4489 eq2480
    | exact resolve eq2480 eq4489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4513 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq1677 eq4507
    | exact resolve eq4507 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4507
  have eq4523 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq1880 eq4513
    | exact resolve eq4513 eq1880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1880 eq4513
  have eq6199 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2633 (M.op sF4 x)
       have i₂ := eq516 sF4 sF3 x
       grind)
    | exact superpose eq516 eq2633
    | exact resolve eq2633 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6250 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq216 eq6199
    | exact resolve eq6199 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6199
  have eq6309 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq6250 eq1052
    | exact resolve eq1052 eq6250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6317 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq4036 eq6309
    | exact resolve eq6309 eq4036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6309
  have eq6448 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) x) x) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq1730 eq2766
    | exact resolve eq2766 eq1730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2766
  have eq6498 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq170 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq170
    | (have j0 := eq170 x
       grind)
    | exact resolve eq170 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq6531 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6498
  have eq6540 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6531
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq6531
    | exact resolve eq6531 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6531
  have eq6559 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2478 eq4045
    | exact resolve eq4045 eq2478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2478
  have eq6708 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4047 X0 X2
       have i₂ := eq4047 X0 X1
       grind)
    | (have i₁ := eq4047 X1 X1
       have i₂ := eq4047 X1 X1
       grind)
    | exact superpose eq4047 eq4047
    | exact resolve eq4047 eq4047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6712 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq4047 x X0
       have i₂ := eq4041
       grind)
    | exact superpose eq4041 eq4047
    | exact resolve eq4047 eq4041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4041
  have eq6713 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq4036 eq4047
    | exact resolve eq4047 eq4036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4036 eq4047
  have eq7002 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) y) (M.op (M.op x X0) X1)) = (M.op (M.op (M.op x X0) (M.op x X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq516 (M.op x X0) X0 X1
       have i₂ := eq6712 X0
       grind)
    | (have i₁ := eq516 (M.op x y) y x
       have i₂ := eq6712 X0
       grind)
    | exact superpose eq6712 eq516
    | exact resolve eq516 eq6712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7014 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) y) (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7002 X0 X1
       have i₂ := eq14 x X0 X0
       grind)
    | exact superpose eq14 eq7002
    | exact resolve eq7002 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7002
  have eq7087 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) X0) X1)) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) X0)) X0) := by
    intro X0 X1
    first
    | exact superpose eq6713 eq516
    | exact resolve eq516 eq6713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7099 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7087 x X1
       have i₂ := eq14 sF2 x x
       grind)
    | exact superpose eq14 eq7087
    | exact resolve eq7087 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7087
  have eq8052 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq95 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq8297 : ∀ X0 : G, (σ X0) ≠ (σ (M.op (M.op X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq729
  have eq8846 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1222 eq499
    | (have j0 := eq499 y X1 X2
       grind)
    | exact resolve eq499 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499 eq1222
  have eq8847 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) x) X1)) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1594 eq8846
    | exact resolve eq8846 eq1594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594 eq8846
  have eq8848 : ∀ X2 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x x) X2)) y) := by
    intro X2
    first
    | exact superpose eq4045 eq8847
    | exact resolve eq8847 eq4045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8847
  have eq8853 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x y) (M.op x X0))) y) := by
    intro X0
    first
    | (have i₁ := eq8848 y
       have i₂ := eq931 X0
       grind)
    | exact superpose eq931 eq8848
    | exact resolve eq8848 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq8864 : ∀ X0 : G, (M.op x x) ≠ (M.op (M.op (M.op x y) x) (M.op (M.op x x) X0)) ∨ y = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x x) X0)) (M.op (M.op (M.op x y) x) (M.op (M.op x x) X0))) ∨ (M.op (M.op (M.op x y) x) (M.op (M.op x x) X0)) = (k y (M.op (M.op (M.op x y) x) (M.op (M.op x x) X0))) := by
    intro X0
    first
    | exact superpose eq8848 eq12
    | (have j0 := eq12 y (M.op (M.op (M.op x y) x) (M.op (M.op x x) X0))
       grind)
    | exact resolve eq12 eq8848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8848
  have eq8890 : ∀ X0 : G, y = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) (M.op (M.op x x) X0)) ∨ (M.op x x) ≠ (M.op (M.op (M.op x y) x) (M.op (M.op x x) X0)) ∨ (M.op (M.op (M.op x y) x) (M.op (M.op x x) X0)) = (k y (M.op (M.op (M.op x y) x) (M.op (M.op x x) X0))) := by
    intro X0
    first
    | (have i₁ := eq8864 X0
       have i₂ := eq516 (M.op sF0 x) (M.op (M.op x x) X0) (M.op (M.op x x) X0)
       grind)
    | exact superpose eq516 eq8864
    | (have j0 := eq8864 X0
       grind)
    | exact resolve eq8864 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8864
  have eq8893 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) y) := by
    first
    | (have i₁ := eq8853 x
       have i₂ := eq516 sF0 x (M.op x x)
       grind)
    | exact superpose eq516 eq8853
    | exact resolve eq8853 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8853
  have eq8907 : ∀ X0 : G, y = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) (M.op (M.op x x) X0)) ∨ (M.op x x) ≠ (M.op (M.op (M.op x y) x) (M.op (M.op x x) X0)) ∨ (M.op (M.op (M.op x y) x) (M.op (M.op x x) X0)) = (k y (M.op (M.op (M.op x y) x) (M.op (M.op x x) X0))) := by
    intro X0
    first
    | (have i₁ := eq8890 X0
       have i₂ := eq516 sF0 x x
       grind)
    | exact superpose eq516 eq8890
    | (have j0 := eq8890 X0
       grind)
    | exact resolve eq8890 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8890
  have eq8910 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) y) := by
    first
    | (have i₁ := eq8893
       have i₂ := eq1052 sF0 x
       grind)
    | exact superpose eq1052 eq8893
    | exact resolve eq8893 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8893
  have eq8920 : ∀ X0 : G, y = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) (M.op (M.op x x) X0)) ∨ (M.op x x) ≠ (M.op (M.op (M.op x y) x) (M.op (M.op x x) X0)) ∨ (M.op (M.op (M.op x y) x) (M.op (M.op x x) X0)) = (k y (M.op (M.op (M.op x y) x) (M.op (M.op x x) X0))) := by
    intro X0
    first
    | (have i₁ := eq8907 X0
       have i₂ := eq1052 sF0 x
       grind)
    | exact superpose eq1052 eq8907
    | (have j0 := eq8907 X0
       grind)
    | exact resolve eq8907 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8907
  have eq8923 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) x) y) := by
    first
    | exact superpose eq1730 eq8910
    | exact resolve eq8910 eq1730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8910
  have eq8932 : ∀ X0 : G, y = (M.op (M.op (M.op (M.op x y) x) x) (M.op (M.op x x) X0)) ∨ (M.op x x) ≠ (M.op (M.op (M.op x y) x) (M.op (M.op x x) X0)) ∨ (M.op (M.op (M.op x y) x) (M.op (M.op x x) X0)) = (k y (M.op (M.op (M.op x y) x) (M.op (M.op x x) X0))) := by
    intro X0
    first
    | exact superpose eq1730 eq8920
    | (have j0 := eq8920 X0
       grind)
    | exact resolve eq8920 eq1730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1730 eq8920
  have eq8978 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1425 eq500
    | (have j0 := eq500 (σ y) X1 X2
       grind)
    | exact resolve eq500 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500 eq1425
  have eq8979 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1588 eq8978
    | exact resolve eq8978 eq1588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8978
  have eq8980 : ∀ X2 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ x)) X2)) (σ y)) := by
    intro X2
    first
    | exact superpose eq4523 eq8979
    | exact resolve eq8979 eq4523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4523 eq8979
  have eq8985 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) (σ y)) := by
    intro X0
    first
    | exact superpose eq932 eq8980
    | exact resolve eq8980 eq932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8980
  have eq9025 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq8985 x
       have i₂ := eq516 sF4 sF2 (M.op sF2 x)
       grind)
    | exact superpose eq516 eq8985
    | exact resolve eq8985 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516 eq8985
  have eq9042 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq9025
       have i₂ := eq1052 sF4 sF2
       grind)
    | exact superpose eq1052 eq9025
    | exact resolve eq9025 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9025
  have eq9055 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1699 eq9042
    | exact resolve eq9042 eq1699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1699 eq9042
  have eq9978 : ∀ X0 : G, x = (M.op (M.op (M.op x x) x) (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq6559 eq2509
    | exact resolve eq2509 eq6559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2509 eq6559
  have eq9983 : ∀ X0 : G, x = (M.op (M.op (M.op x y) y) (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq9978 X0
       have i₂ := eq6712 x
       grind)
    | exact superpose eq6712 eq9978
    | exact resolve eq9978 eq6712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9978
  have eq10465 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) X0) X0) y) := by
    intro X0
    first
    | (have i₁ := eq8923
       have i₂ := eq6708 sF0 x x
       grind)
    | (have i₁ := eq8923
       have i₂ := eq6708 sF0 x x
       grind)
    | exact superpose eq6708 eq8923
    | exact resolve eq8923 eq6708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8923
  have eq15178 : ∀ X0 : G, (σ x) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq722 x x X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq722
    | (have j0 := eq722 x x x
       grind)
    | exact resolve eq722 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq722
  have eq15321 : ∀ X0 : G, (σ x) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq15178 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15178
  have eq15359 : ∀ X0 : G, (σ x) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15321 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15321
    | (have j0 := eq15321 X0
       grind)
    | exact resolve eq15321 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15321
  have eq15412 : ∀ X0 : G, (σ x) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15359 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15359
    | (have j0 := eq15359 X0
       grind)
    | exact resolve eq15359 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15359
  have eq15752 : ∀ X0 X1 : G, (M.op x x) = (M.op x (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq7014 eq2608
    | exact resolve eq2608 eq7014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2608 eq7014
  have eq15865 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq7099 eq2633
    | exact resolve eq2633 eq7099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2633 eq7099
  have eq42328 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq113 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42338 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq42328
    | exact resolve eq42328 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42328
  have eq42349 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq42338
       have r₂ := eq28
       grind)
    | exact resolve eq42338 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42338
  have eq42351 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq42349
    | exact resolve eq42349 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42349
  have eq42394 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq42351 eq1022
    | exact resolve eq1022 eq42351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022 eq42351
  have eq42449 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq42394
    | exact resolve eq42394 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42394
  have eq42544 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2587 x x
       have i₂ := eq42449
       grind)
    | exact superpose eq42449 eq2587
    | exact resolve eq2587 eq42449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42449
  have eq42554 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq42544
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq42544
    | exact resolve eq42544 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42544
  have eq42598 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42554 eq2969
    | exact resolve eq2969 eq42554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2969
  have eq42620 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ y) (σ x)) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42554 eq9055
    | exact resolve eq9055 eq42554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9055 eq42554
  have eq42639 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq42620
       have i₂ := eq4022 sF3 sF2
       grind)
    | exact superpose eq4022 eq42620
    | exact resolve eq42620 eq4022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42620
  have eq42641 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq42598
    | exact resolve eq42598 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42598
  have eq67940 : (σ x) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42641 eq15412
    | (have j0 := eq15412 (σ y)
       grind)
    | exact resolve eq15412 eq42641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15412 eq42641
  have eq67974 : (σ x) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq67940
  have eq97684 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq67974 eq2480
    | exact resolve eq2480 eq67974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67974
  have eq97705 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6713 eq97684
    | exact resolve eq97684 eq6713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97684
  have eq135194 : (k (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq97705 eq2480
    | exact resolve eq2480 eq97705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97705
  have eq135217 : (k (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2484 eq135194
    | exact resolve eq135194 eq2484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2484 eq135194
  have eq135229 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4252 eq135217
    | exact resolve eq135217 eq4252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4252 eq135217
  have eq135239 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq135229 eq50
    | exact resolve eq50 eq135229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135229
  have eq135316 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42639 eq135239
    | exact resolve eq135239 eq42639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42639 eq135239
  have eq135488 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq135316
  have eq135500 : y = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq135488
    | exact resolve eq135488 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135488
  have eq135531 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq135500
       grind)
    | exact superpose eq135500 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq135500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135550 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq135531
  have eq312697 : ∀ X1 : G, (M.op (M.op (M.op x y) x) (M.op x x)) = (M.op (M.op (M.op x y) x) (M.op (M.op x x) X1)) := by
    intro X1
    first
    | exact superpose eq4045 eq3874
    | exact resolve eq3874 eq4045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3874 eq4045
  have eq320622 : y = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2587 x x
       have i₂ := eq135550
       grind)
    | exact superpose eq135550 eq2587
    | exact resolve eq2587 eq135550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135550
  have eq320666 : y = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq320622
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq320622
    | exact resolve eq320622 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320622
  have eq320667 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq320666
  have eq320783 : (k x x) = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq320667
  have eq324215 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq135500
       have i₂ := eq320783
       grind)
    | exact superpose eq320783 eq135500
    | exact resolve eq135500 eq320783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135500 eq320783
  have eq324263 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq324215
  have eq324489 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2587 x x
       have i₂ := eq324263
       grind)
    | exact superpose eq324263 eq2587
    | exact resolve eq2587 eq324263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324263
  have eq324534 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq324489
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq324489
    | exact resolve eq324489 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324489
  have eq324535 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq324534
  have eq324571 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq324535 eq28
    | exact resolve eq28 eq324535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324574 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq324535 eq76
    | (have r₁ := eq76
       have r₂ := eq324535
       grind)
    | exact resolve eq76 eq324535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq324582 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq324535 eq1677
    | exact resolve eq1677 eq324535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324602 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ x)) X0)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq324535 eq4489
    | exact resolve eq4489 eq324535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4489
  have eq324652 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq324574
  have eq324681 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15865 eq324602
    | exact resolve eq324602 eq15865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15865 eq324602
  have eq324688 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1373 eq324582
    | exact resolve eq324582 eq1373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324582
  have eq324705 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1373 eq324681
    | exact resolve eq324681 eq1373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373 eq324681
  have eq324710 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1588 eq324688
    | exact resolve eq324688 eq1588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324688
  have eq324722 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1588 eq324705
    | exact resolve eq324705 eq1588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324705
  have eq325015 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq324535 eq324710
    | exact resolve eq324710 eq324535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324710
  have eq325220 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq325015
  have eq329031 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq325220 eq932
    | exact resolve eq932 eq325220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq329080 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  have eq329274 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq329031
    | exact resolve eq329031 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329031
  have eq331492 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq329274 eq1693
    | exact resolve eq1693 eq329274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693
  have eq331725 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1588 eq331492
    | exact resolve eq331492 eq1588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1588 eq331492
  have eq331874 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq324722 eq329274
    | exact resolve eq329274 eq324722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324722 eq329274
  have eq331952 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq331874
  have eq333414 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq329080 eq50
    | exact resolve eq50 eq329080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq329080
  have eq335905 : (τ (σ x)) = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq325220 eq333414
    | exact resolve eq333414 eq325220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325220
  have eq335906 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq331952 eq333414
    | exact resolve eq333414 eq331952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331952 eq333414
  have eq336241 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq335906
  have eq336242 : (τ (σ x)) = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq335905
  have eq336258 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq336242
    | exact resolve eq336242 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336242
  have eq336316 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq336258
       grind)
    | exact superpose eq336258 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq336258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq336338 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq336316
  have eq336514 : (k x x) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq336338
  have eq340705 : x = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq336258
       have i₂ := eq336241
       grind)
    | exact superpose eq336241 eq336258
    | exact resolve eq336258 eq336241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336258
  have eq340743 : x = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq340705
  have eq340914 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq340743 eq417
    | exact resolve eq417 eq340743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417 eq340743
  have eq341244 : ∀ X0 : G, (τ (k X0 (σ x))) = (τ (k X0 (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq340914 X0
       have i₂ := eq432 X0
       grind)
    | exact superpose eq432 eq340914
    | exact resolve eq340914 eq432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340914
  have eq342666 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq336241
       have i₂ := eq336514
       grind)
    | exact superpose eq336514 eq336241
    | exact resolve eq336241 eq336514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336241 eq336514
  have eq342700 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq342666
  have eq342846 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op x (M.op (τ (M.op (σ x) (σ y))) X0)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq15752 x x
       have i₂ := eq342700
       grind)
    | exact superpose eq342700 eq15752
    | exact resolve eq15752 eq342700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342869 : (k (τ (M.op (σ x) (σ y))) x) = (M.op (τ (M.op (σ x) (σ y))) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq342700
  have eq343009 : (τ (k (M.op (σ x) (σ y)) (σ x))) = (M.op (τ (M.op (σ x) (σ y))) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq342869
       have i₂ := eq432 sF4
       grind)
    | exact superpose eq432 eq342869
    | exact resolve eq342869 eq432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432 eq342869
  have eq448875 : (τ (k (M.op (σ x) (σ y)) (σ x))) = (τ (M.op (M.op (σ x) (σ y)) (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq331725 eq341244
    | exact resolve eq341244 eq331725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331725 eq341244
  have eq449300 : (τ (k (M.op (σ x) (σ y)) (σ x))) = (τ (M.op (M.op (σ x) (σ y)) (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq448875
  have eq490761 : (τ (M.op (σ x) (σ y))) = (M.op x (τ (k (M.op (σ x) (σ y)) (σ x)))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq343009 eq342846
    | exact resolve eq342846 eq343009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342846 eq343009
  have eq490820 : (τ (M.op (σ x) (σ y))) = (M.op x (τ (k (M.op (σ x) (σ y)) (σ x)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq490761
  have eq627524 : (τ (M.op (σ x) (σ y))) = (M.op x (τ (M.op (M.op (σ x) (σ y)) (σ x)))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq449300 eq490820
    | exact resolve eq490820 eq449300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449300 eq490820
  have eq627691 : (τ (M.op (σ x) (σ y))) = (M.op x (τ (M.op (M.op (σ x) (σ y)) (σ x)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq627524
  have eq762032 : (τ (σ x)) = (M.op x (τ (M.op (σ x) (σ x)))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq324535 eq627691
    | exact resolve eq627691 eq324535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324535 eq627691
  have eq762262 : (τ (σ x)) = (M.op x (τ (M.op (σ x) (σ x)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq762032
  have eq762289 : x = (M.op x (τ (M.op (σ x) (σ x)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq762262
    | exact resolve eq762262 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762262
  have eq1230722 : ∀ X0 : G, (M.op x x) ≠ (M.op (M.op (M.op x y) x) (M.op x x)) ∨ y = (M.op (M.op (M.op (M.op x y) x) x) (M.op (M.op x x) X0)) ∨ (M.op (M.op (M.op x y) x) (M.op (M.op x x) X0)) = (k y (M.op (M.op (M.op x y) x) (M.op (M.op x x) X0))) := by
    intro X0
    first
    | exact superpose eq312697 eq8932
    | (have j0 := eq8932 X0
       grind)
    | exact resolve eq8932 eq312697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8932
  have eq1230723 : ∀ X0 : G, (M.op x x) ≠ (M.op (M.op (M.op x y) x) (M.op x x)) ∨ (M.op (M.op (M.op x y) x) (M.op x x)) = (k y (M.op (M.op (M.op x y) x) (M.op x x))) ∨ y = (M.op (M.op (M.op (M.op x y) x) x) (M.op (M.op x x) X0)) := by
    intro X0
    first
    | exact superpose eq312697 eq1230722
    | (have j0 := eq1230722 X0
       grind)
    | exact resolve eq1230722 eq312697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312697 eq1230722
  have eq1291440 : x = (M.op x (τ (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq324652 eq762289
    | exact resolve eq762289 eq324652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324652 eq762289
  have eq1291765 : x = (M.op x (τ (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq1291440
  have eq1291888 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq30 eq1291765
    | exact resolve eq1291765 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1291765
  have eq1291922 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1291888
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1291888
    | exact resolve eq1291888 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291888
  have eq1291923 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1291922
  have eq1291949 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1291923 eq113
    | exact resolve eq113 eq1291923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq1291923
  have eq1292038 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq1291949
  have eq1292073 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1292038
       have r₂ := eq324571
       grind)
    | exact resolve eq1292038 eq324571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324571 eq1292038
  have eq1292372 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2587 x x
       have i₂ := eq1292073
       grind)
    | exact superpose eq1292073 eq2587
    | exact resolve eq2587 eq1292073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292073
  have eq1292504 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1292372
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1292372
    | exact resolve eq1292372 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292372
  have eq1292505 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1292504
  have eq1292603 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1292505 eq21
    | exact resolve eq21 eq1292505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1292758 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1292505 eq2963
    | exact resolve eq2963 eq1292505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2963
  have eq1292852 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op y X0) X0) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1292505 eq10465
    | exact resolve eq10465 eq1292505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10465
  have eq1293056 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq1292505
  have eq1293088 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1292852 x
       have i₂ := eq4022 y x
       grind)
    | exact superpose eq4022 eq1292852
    | exact resolve eq1292852 eq4022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292852
  have eq1293121 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1292758
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1292758
    | exact resolve eq1292758 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292758
  have eq1293246 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1292603
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1292603
    | exact resolve eq1292603 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292603
  have eq1293357 : (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1293246 eq2637
    | exact resolve eq2637 eq1293246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2637
  have eq1293358 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1293246 eq3061
    | exact resolve eq3061 eq1293246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3061
  have eq1294261 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6317 eq1293357
    | exact resolve eq1293357 eq6317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6317 eq1293357
  have eq1294353 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq1293088
       grind)
    | exact superpose eq1293088 eq110
    | exact resolve eq110 eq1293088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293088
  have eq1294802 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1294353
       have r₂ := eq1293056
       grind)
    | exact resolve eq1294353 eq1293056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293056 eq1294353
  have eq1294824 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1294802
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1294802
    | exact resolve eq1294802 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294802
  have eq1294866 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq1293121
       grind)
    | exact superpose eq1293121 eq110
    | exact resolve eq110 eq1293121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq1293121
  have eq1295261 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1294866
  have eq1295373 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq1295261
    | exact resolve eq1295261 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295261
  have eq1296006 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq6540 eq1294824
    | exact resolve eq1294824 eq6540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6540 eq1294824
  have eq1304587 : (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) = (k (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1294261 eq963
    | exact resolve eq963 eq1294261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963 eq1294261
  have eq1304839 : (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq216 eq1304587
    | exact resolve eq1304587 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq1304587
  have eq1304868 : (M.op (σ x) (σ x)) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6250 eq1304839
    | exact resolve eq1304839 eq6250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6250 eq1304839
  have eq1737090 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1296006 eq2587
    | exact resolve eq2587 eq1296006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2587 eq1296006
  have eq1737287 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq1737090
    | exact resolve eq1737090 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1737090
  have eq1737757 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1737287 eq4022
    | exact resolve eq4022 eq1737287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4022 eq1737287
  have eq1737951 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6713 eq1737757
    | exact resolve eq1737757 eq6713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6713 eq1737757
  have eq1738891 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1293246 eq1737951
    | exact resolve eq1737951 eq1293246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293246 eq1737951
  have eq1739317 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq1738891
  have eq1739425 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1739317
       have r₂ := eq28
       grind)
    | exact resolve eq1739317 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1739317
  have eq1739610 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1739425 eq1293358
    | exact resolve eq1293358 eq1739425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293358
  have eq1739615 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1739425 eq1304868
    | exact resolve eq1304868 eq1739425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304868 eq1739425
  have eq1739780 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1739615
  have eq1739785 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1739610
  have eq1747940 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1739780 eq1295373
    | exact resolve eq1295373 eq1739780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295373 eq1739780
  have eq1748098 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1747940
  have eq1748412 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1748098 eq1739785
    | exact resolve eq1739785 eq1748098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1739785 eq1748098
  have eq1748762 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1748412
  have eq1748960 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1748762 eq29
    | exact resolve eq29 eq1748762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1748762
  have eq1750876 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq1748960
    | exact resolve eq1748960 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1748960
  have eq1750877 : x = (M.op x y) := by grind
  clear eq1750876
  have eq1750882 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1750877 eq21
    | exact resolve eq21 eq1750877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq1751125 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op x X0) x)) := by
    intro X0
    first
    | exact superpose eq1750877 eq9983
    | exact resolve eq9983 eq1750877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9983
  have eq1751296 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op x X0) x)) := by
    intro X0
    first
    | (have i₁ := eq1751125 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1751125
    | (have j0 := eq1751125 X0
       grind)
    | exact resolve eq1751125 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751125
  have eq1751463 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1750882
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1750882
    | exact resolve eq1750882 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750882
  have eq1751509 : ∀ X0 : G, x = (M.op x (M.op (M.op x X0) x)) := by
    intro X0
    first
    | exact superpose eq1750877 eq1751296
    | exact resolve eq1751296 eq1750877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751296
  have eq1751569 : x = (M.op x x) := by
    first
    | (have i₁ := eq1751509 x
       have i₂ := eq15752 x x
       grind)
    | exact superpose eq15752 eq1751509
    | exact resolve eq1751509 eq15752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15752 eq1751509
  have eq1751746 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1751463 eq27
    | exact resolve eq27 eq1751463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1751835 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq1751463 eq1677
    | exact resolve eq1677 eq1751463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1677
  have eq1753055 : ∀ X0 : G, x ≠ (M.op (M.op (M.op x y) x) x) ∨ (M.op (M.op (M.op x y) x) x) = (k y (M.op (M.op (M.op x y) x) x)) ∨ y = (M.op (M.op (M.op (M.op x y) x) x) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1230723 X0
       have i₂ := eq1751569
       grind)
    | exact superpose eq1751569 eq1230723
    | exact resolve eq1230723 eq1751569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230723
  have eq1753180 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8297 x
       have i₂ := eq1751569
       grind)
    | exact superpose eq1751569 eq8297
    | exact resolve eq8297 eq1751569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8297
  have eq1753356 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1753180
  have eq1753456 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1753356
       have i₂ := eq1751569
       grind)
    | exact superpose eq1751569 eq1753356
    | exact resolve eq1753356 eq1751569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751569 eq1753356
  have eq1753457 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1753456
  have eq1753515 : ∀ X0 : G, x ≠ (M.op (M.op x x) x) ∨ (M.op (M.op (M.op x y) x) x) = (k y (M.op (M.op (M.op x y) x) x)) ∨ y = (M.op (M.op (M.op (M.op x y) x) x) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq1750877 eq1753055
    | (have j0 := eq1753055 X0
       grind)
    | exact resolve eq1753055 eq1750877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753055
  have eq1753624 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1753457
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1753457
    | exact resolve eq1753457 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753457
  have eq1753666 : ∀ X0 : G, x ≠ (M.op (M.op x y) y) ∨ (M.op (M.op (M.op x y) x) x) = (k y (M.op (M.op (M.op x y) x) x)) ∨ y = (M.op (M.op (M.op (M.op x y) x) x) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1753515 X0
       have i₂ := eq6712 x
       grind)
    | exact superpose eq6712 eq1753515
    | (have j0 := eq1753515 X0
       grind)
    | exact resolve eq1753515 eq6712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753515
  have eq1753741 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1751463 eq1753624
    | exact resolve eq1753624 eq1751463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753624
  have eq1753769 : ∀ X0 : G, x ≠ (M.op x y) ∨ (M.op (M.op (M.op x y) x) x) = (k y (M.op (M.op (M.op x y) x) x)) ∨ y = (M.op (M.op (M.op (M.op x y) x) x) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq1750877 eq1753666
    | (have j0 := eq1753666 X0
       grind)
    | exact resolve eq1753666 eq1750877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753666
  have eq1753841 : ∀ X0 : G, x ≠ (M.op x y) ∨ (M.op (M.op (M.op x y) x) x) = (k y (M.op (M.op (M.op x y) x) x)) ∨ y = (M.op (M.op (M.op (M.op x y) x) x) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1753769 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1753769
    | (have j0 := eq1753769 X0
       grind)
    | exact resolve eq1753769 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753769
  have eq1753886 : ∀ X0 : G, (M.op (M.op (M.op x y) x) x) = (k y (M.op (M.op (M.op x y) x) x)) ∨ y = (M.op (M.op (M.op (M.op x y) x) x) (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq1753841 X0
       grind)
    | (have r₁ := eq1753841 X0
       have r₂ := eq1750877
       grind)
    | exact resolve eq1753841 eq1750877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753841
  have eq1753912 : ∀ X0 : G, (M.op (M.op x x) x) = (k y (M.op (M.op x x) x)) ∨ y = (M.op (M.op (M.op (M.op x y) x) x) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq1750877 eq1753886
    | (have j0 := eq1753886 X0
       grind)
    | exact resolve eq1753886 eq1750877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753886
  have eq1753933 : ∀ X0 : G, (M.op (M.op x y) y) = (k y (M.op (M.op x y) y)) ∨ y = (M.op (M.op (M.op (M.op x y) x) x) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1753912 X0
       have i₂ := eq6712 x
       grind)
    | exact superpose eq6712 eq1753912
    | (have j0 := eq1753912 X0
       grind)
    | exact resolve eq1753912 eq6712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6712 eq1753912
  have eq1753949 : ∀ X0 : G, (M.op x y) = (k y (M.op x y)) ∨ y = (M.op (M.op (M.op (M.op x y) x) x) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq1750877 eq1753933
    | (have j0 := eq1753933 X0
       grind)
    | exact resolve eq1753933 eq1750877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753933
  have eq1753955 : ∀ X0 : G, (M.op x y) = (k y (M.op x y)) ∨ y = (M.op (M.op (M.op (M.op x y) x) x) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1753949 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1753949
    | (have j0 := eq1753949 X0
       grind)
    | exact resolve eq1753949 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1753949
  have eq1753960 : ∀ X0 : G, x = (k y x) ∨ y = (M.op (M.op (M.op (M.op x y) x) x) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq1750877 eq1753955
    | (have j0 := eq1753955 X0
       grind)
    | exact resolve eq1753955 eq1750877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753955
  have eq1753965 : y = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq6448 eq1753960
    | exact resolve eq1753960 eq6448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6448 eq1753960
  have eq1753970 : x = (k y x) ∨ x = y := by
    first
    | exact superpose eq1750877 eq1753965
    | exact resolve eq1753965 eq1750877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750877 eq1753965
  have eq1766982 : (M.op (M.op (σ (M.op x y)) (σ y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1751835 eq2480
    | exact resolve eq2480 eq1751835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2480
  have eq1767109 : (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq1766982
       have i₂ := eq1052 sF1 sF3
       grind)
    | exact superpose eq1052 eq1766982
    | exact resolve eq1766982 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052 eq1766982
  have eq1767195 : (M.op (σ (M.op x y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1753741 eq1767109
    | exact resolve eq1767109 eq1753741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1767109
  have eq1767242 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1751746 eq1767195
    | exact resolve eq1767195 eq1751746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751746 eq1767195
  have eq1767447 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq1767242 eq1751835
    | exact resolve eq1751835 eq1767242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1767521 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X0) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1767242 eq6708
    | exact resolve eq6708 eq1767242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6708
  have eq1767609 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq1767242 eq1767521
    | exact resolve eq1767521 eq1767242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1767521
  have eq1824738 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8052 x
       have i₂ := eq1753970
       grind)
    | exact superpose eq1753970 eq8052
    | (have j0 := eq8052 x
       grind)
    | exact resolve eq8052 eq1753970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8052 eq1753970
  have eq1824792 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq1824738
  have eq1824836 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1824792
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1824792
    | exact resolve eq1824792 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1824792
  have eq1824930 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq27 eq1824836
    | exact resolve eq1824836 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1824836
  have eq1825016 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq1751463 eq1824930
    | exact resolve eq1824930 eq1751463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1824930
  have eq1825101 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq1825016
       have r₂ := eq28
       grind)
    | exact resolve eq1825016 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1825016
  have eq1825165 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1825101
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1825101
    | exact resolve eq1825101 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1825101
  have eq1825223 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1751463 eq1825165
    | exact resolve eq1825165 eq1751463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1825165
  have eq1825274 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1753741 eq1825223
    | exact resolve eq1825223 eq1753741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753741 eq1825223
  have eq1826290 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1825274 eq1751835
    | exact resolve eq1751835 eq1825274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751835 eq1825274
  have eq1826316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1767609 eq1826290
    | exact resolve eq1826290 eq1767609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1767609 eq1826290
  have eq1826496 : x = y := by
    first
    | (have r₁ := eq1826316
       have r₂ := eq28
       grind)
    | exact resolve eq1826316 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1826316
  have eq1827031 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1826496
       grind)
    | exact superpose eq1826496 eq25
    | exact resolve eq25 eq1826496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1826496
  have eq1828000 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1827031
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1827031
    | exact resolve eq1827031 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1827031
  have eq1828215 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1751463 eq1828000
    | exact resolve eq1828000 eq1751463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751463 eq1828000
  have eq1870171 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1828215 eq1767447
    | exact resolve eq1767447 eq1828215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1767447 eq1828215
  have eq1870193 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1767242 eq1870171
    | exact resolve eq1870171 eq1767242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1767242 eq1870171
  have eq1870398 : False := by grind
  exact eq1870398

/-- `Equation2683`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_y_pxy_Equation2683 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2683 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2683.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X0) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
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
  have eq62 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op X0 x) (M.op x x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (M.op X0 X1) (M.op (M.op X0 X1) X1)
       have i₂ := eq9 (M.op X0 X1) X1 X0
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq62 X0 (M.op X0 X0)
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq314 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq313 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq313
    | (have j0 := eq313 (σ X0) (σ X1)
       grind)
    | exact resolve eq313 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq315 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq313 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq313
    | (have j0 := eq313 (τ X0) (τ X1)
       grind)
    | exact resolve eq313 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq334 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq313 (τ X0) X1
       grind)
    | exact superpose eq313 eq17
    | (have j1 := eq313 (τ X0) X1
       grind)
    | exact resolve eq17 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq334 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq67 (τ X0)
       grind)
    | exact superpose eq67 eq334
    | (have j0 := eq334 X0 (τ X0)
       grind)
    | exact resolve eq334 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k X0 (k X0 (σ (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | exact superpose eq334 eq433
    | (have j0 := eq433 X0
       have j1 := eq334 X0 (τ X0)
       grind)
    | exact resolve eq433 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq433
  have eq449 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq447 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq447
    | (have j0 := eq447 X0
       grind)
    | exact resolve eq447 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq511 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (k (τ X0) (τ X0))
       have i₂ := eq449 (τ X0)
       grind)
    | exact superpose eq449 eq17
    | (have j1 := eq449 (τ X0)
       grind)
    | exact resolve eq17 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq516 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k X0 (k X0 (σ (τ X0)))) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq511 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq511
    | (have j0 := eq511 X0
       grind)
    | exact resolve eq511 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq532 : ∀ X0 : G, (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (k X0 X0) = (k X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq516 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq516
    | (have j0 := eq516 X0
       grind)
    | exact resolve eq516 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq669 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq314 X0 X1
       have i₂ := eq313 X0 X1
       grind)
    | exact superpose eq313 eq314
    | (have j0 := eq314 X0 X1
       have j1 := eq313 (σ X0) (σ X1)
       grind)
    | exact resolve eq314 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 X1))) = (k (σ X2) (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 X1)
       have i₂ := eq314 X0 X1
       grind)
    | exact superpose eq314 eq15
    | (have j1 := eq314 X0 X1
       grind)
    | exact resolve eq15 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq812 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq315 X0 X0
       grind)
    | exact superpose eq315 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq315 X0 X0
       grind)
    | (have r₁ := eq12 X0 (τ X1)
       have r₂ := eq315 X1 X1
       grind)
    | exact resolve eq12 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq813 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ (k X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq67 (τ x)
       have i₂ := eq315 x x
       grind)
    | exact superpose eq315 eq67
    | (have j1 := eq315 X0 X0
       grind)
    | exact resolve eq67 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq822 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq315 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq824 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq812 X0 X1
       have j1 := eq12 X1 (τ X0)
       grind)
    | (have r₁ := eq812 X0 X1
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq812 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq835 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq822 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq822
    | (have j0 := eq822 (σ X0) (σ X1)
       grind)
    | exact resolve eq822 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq845 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 X1) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq835 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq835
    | (have j0 := eq835 X0 X1
       grind)
    | exact resolve eq835 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq847 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq845 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq845
    | (have j0 := eq845 X0 X1
       grind)
    | exact resolve eq845 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq848 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq847 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq847
    | (have j0 := eq847 X0 X1
       grind)
    | exact resolve eq847 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq849 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq848 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq848
    | (have j0 := eq848 X0 X1
       grind)
    | exact resolve eq848 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq854 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq849 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq849
    | (have j0 := eq849 (σ X0) (σ X1)
       grind)
    | exact resolve eq849 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq912 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq824 (σ X0) X1
       have i₂ := eq28 X0 (σ X0)
       grind)
    | exact superpose eq28 eq824
    | (have j0 := eq824 (σ X0) X1
       grind)
    | exact resolve eq824 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq913 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq912 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq912
    | (have j0 := eq912 X0 X1
       grind)
    | exact resolve eq912 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq916 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq913 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq913
    | (have j0 := eq913 X0 X1
       grind)
    | exact resolve eq913 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq921 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq916 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq916
    | (have j0 := eq916 (σ X0) X1
       grind)
    | exact resolve eq916 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq3827 : ∀ X0 X1 : G, (τ (τ X0)) ≠ (τ (τ X0)) ∨ (k X1 (τ (τ X0))) = (M.op X1 (τ (τ X0))) ∨ (k X0 X0) = (k X0 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ (τ X0))
       have i₂ := eq532 X0
       grind)
    | exact superpose eq532 eq12
    | (have j0 := eq12 X1 (τ (τ X0))
       have j1 := eq532 X0
       grind)
    | (have r₁ := eq12 X0 (τ (τ X0))
       have r₂ := eq532 X0
       grind)
    | exact resolve eq12 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3844 : ∀ X0 X1 : G, (k X1 (τ (τ X0))) = (M.op X1 (τ (τ X0))) ∨ (k X0 X0) = (k X0 (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3827 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3827
  have eq4125 : ∀ X0 X1 : G, (σ (M.op (τ (τ X0)) (τ (τ X0)))) ≠ (σ (τ (τ X0))) ∨ (k X1 (σ (τ (τ X0)))) = (M.op X1 (σ (τ (τ X0)))) ∨ (k X0 X0) = (k X0 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq921 (τ (τ X0)) X1
       have i₂ := eq3844 X0 (τ (τ X0))
       grind)
    | exact superpose eq3844 eq921
    | (have j0 := eq921 (τ (τ X0)) X1
       have j1 := eq3844 X0 X1
       grind)
    | exact resolve eq921 eq3844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3844
  have eq4179 : ∀ X0 X1 : G, (τ X0) ≠ (σ (M.op (τ (τ X0)) (τ (τ X0)))) ∨ (k X1 (σ (τ (τ X0)))) = (M.op X1 (σ (τ (τ X0)))) ∨ (k X0 X0) = (k X0 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4125 X0 X1
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq4125
    | (have j0 := eq4125 X0 X1
       grind)
    | exact resolve eq4125 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4125
  have eq4187 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (τ X0) ≠ (σ (M.op (τ (τ X0)) (τ (τ X0)))) ∨ (k X0 X0) = (k X0 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4179 X0 X1
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq4179
    | (have j0 := eq4179 X0 X1
       grind)
    | exact resolve eq4179 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4179
  have eq4191 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (τ X0) ≠ (σ (τ (τ X0))) ∨ (k X0 X0) = (k X0 (k X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq532 eq4187
    | (have j0 := eq4187 X0 X1
       have j1 := eq532 X0
       grind)
    | exact resolve eq4187 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532 eq4187
  have eq4193 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (k X0 X0) = (k X0 (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4191 X0 X1
       grind)
    | (have r₁ := eq4191 X0 X1
       have r₂ := eq11 (τ X0)
       grind)
    | exact resolve eq4191 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4191
  have eq4225 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) ∨ (k X0 X0) = (k X0 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq921 (τ X0) X1
       have i₂ := eq4193 X0 (τ X0)
       grind)
    | exact superpose eq4193 eq921
    | (have j0 := eq921 (τ X0) X1
       have j1 := eq4193 X0 X1
       grind)
    | exact resolve eq921 eq4193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4193
  have eq4293 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) ∨ (k X0 X0) = (k X0 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4225 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4225
    | (have j0 := eq4225 X0 X1
       grind)
    | exact resolve eq4225 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4225
  have eq4299 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 X0) = (k X0 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4293 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4293
    | (have j0 := eq4293 X0 X1
       grind)
    | exact resolve eq4293 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4293
  have eq4302 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ (τ X0)) ≠ X0 ∨ (k X0 X0) = (k X0 (k X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq449 eq4299
    | (have j0 := eq4299 X0 X1
       have j1 := eq449 X0
       grind)
    | exact resolve eq4299 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449 eq4299
  have eq4303 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq4302 X0 X1
       grind)
    | (have r₁ := eq4302 X0 X1
       have r₂ := eq11 X0
       grind)
    | exact resolve eq4302 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4302
  have eq4304 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4303 X1 X1
       have i₂ := eq313 X1 X1
       grind)
    | exact superpose eq313 eq4303
    | (have j0 := eq4303 X0 X1
       have j1 := eq313 X1 X0
       grind)
    | exact resolve eq4303 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4327 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k X0 (τ (k (σ X0) (σ X0)))) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (k (σ X0) (σ X0))
       have i₂ := eq4303 (σ X0) X1
       grind)
    | exact superpose eq4303 eq28
    | (have j1 := eq4303 (σ X0) X1
       grind)
    | exact resolve eq28 eq4303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4303
  have eq4378 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k X0 (k (τ (σ X0)) X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4327 X1 X1
       have i₂ := eq22 (σ X1) X1
       grind)
    | exact superpose eq22 eq4327
    | (have j0 := eq4327 X0 X1
       grind)
    | exact resolve eq4327 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4327
  have eq4393 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq4304 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq4304 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq4304 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4304
  have eq4419 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (k X0 X0) = (k X0 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4378 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4378
    | (have j0 := eq4378 X0 X1
       grind)
    | exact resolve eq4378 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4378
  have eq13728 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq669 x y
       grind)
    | exact superpose eq669 eq16
    | (have j1 := eq669 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq669 x y
       grind)
    | exact resolve eq16 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq13785 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13728
  have eq13856 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13785
       grind)
    | exact superpose eq13785 eq16
    | exact resolve eq16 eq13785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13866 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (σ x)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ x)
       have i₂ := eq13785
       grind)
    | exact superpose eq13785 eq9
    | exact resolve eq9 eq13785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13867 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq13785
       grind)
    | exact superpose eq13785 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq13785
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq13785
       grind)
    | exact resolve eq13 eq13785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13876 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq66 (σ x) (σ y)
       have i₂ := eq13785
       grind)
    | exact superpose eq13785 eq66
    | exact resolve eq66 eq13785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13890 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13867
  have eq13901 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13785 eq13876
    | exact resolve eq13876 eq13785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13876
  have eq13904 : (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13890
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq13890
    | exact resolve eq13890 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13890
  have eq13915 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq313 eq13904
    | (have j1 := eq313 (σ y) (σ y)
       grind)
    | exact resolve eq13904 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq13904
  have eq13937 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq13901
       grind)
    | exact superpose eq13901 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq13901
       grind)
    | exact resolve eq12 eq13901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13969 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq13937 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13937
  have eq14039 : (τ (M.op (σ x) (σ x))) = (M.op (τ (σ x)) (τ (M.op (σ x) (σ x)))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq813 (σ x)
       have i₂ := eq13969 (σ x)
       grind)
    | exact superpose eq13969 eq813
    | (have j0 := eq813 (σ x)
       grind)
    | exact resolve eq813 eq13969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813 eq13969
  have eq14145 : (τ (M.op (σ x) (σ x))) = (M.op x (τ (M.op (σ x) (σ x)))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14039
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq14039
    | exact resolve eq14039 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14039
  have eq14160 : x = (M.op x x) ∨ (τ (M.op (σ x) (σ x))) = (M.op x (τ (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14145
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq14145
    | exact resolve eq14145 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14145
  have eq14167 : x = (M.op x x) ∨ (τ (σ x)) = (M.op x (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13901 eq14160
    | exact resolve eq14160 eq13901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13901 eq14160
  have eq14172 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14167
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq14167
    | exact resolve eq14167 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14167
  have eq14173 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq14172
  have eq14187 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq66 x y
       have i₂ := eq14173
       grind)
    | exact superpose eq14173 eq66
    | exact resolve eq66 eq14173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq14209 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq14173 eq14187
    | exact resolve eq14187 eq14173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14173 eq14187
  have eq14210 : x = (M.op x x) := by grind
  clear eq14209
  have eq14216 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq14210
       grind)
    | exact superpose eq14210 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq14210
       grind)
    | exact resolve eq12 eq14210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14248 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq14216 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14216
  have eq14271 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq921 x X0
       have i₂ := eq14248 x
       grind)
    | exact superpose eq14248 eq921
    | (have j0 := eq921 x X0
       grind)
    | exact resolve eq921 eq14248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14324 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14271 X0
       have i₂ := eq14210
       grind)
    | exact superpose eq14210 eq14271
    | (have j0 := eq14271 X0
       grind)
    | exact resolve eq14271 eq14210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14210 eq14271
  have eq14325 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq14324 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14324
  have eq14490 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq22 X0 x
       have i₂ := eq14325 X0
       grind)
    | exact superpose eq14325 eq22
    | exact resolve eq22 eq14325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq14529 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq14325 (σ X0)
       grind)
    | exact superpose eq14325 eq15
    | exact resolve eq15 eq14325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14325
  have eq14619 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq14529 X0
       have i₂ := eq14248 X0
       grind)
    | exact superpose eq14248 eq14529
    | exact resolve eq14529 eq14248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14529
  have eq14643 : ∀ X0 : G, (τ (M.op X0 (σ x))) = (M.op (τ X0) x) := by
    intro X0
    first
    | (have i₁ := eq14490 X0
       have i₂ := eq14248 (τ X0)
       grind)
    | exact superpose eq14248 eq14490
    | exact resolve eq14490 eq14248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14248 eq14490
  have eq15391 : ∀ X0 X1 : G, (τ (σ x)) = (M.op (τ (M.op (M.op (σ x) X0) (M.op X1 X0))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq14643 (M.op (M.op (σ x) X0) (M.op X1 X0))
       have i₂ := eq9 (σ x) X0 X1
       grind)
    | exact superpose eq9 eq14643
    | exact resolve eq14643 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14643
  have eq15500 : ∀ X0 X1 : G, x = (M.op (τ (M.op (M.op (σ x) X0) (M.op X1 X0))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq15391 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15391
    | exact resolve eq15391 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15391
  have eq21188 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (k X0 X0))) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4393 (σ X0) X1
       have i₂ := eq693 X0 X0 X0
       grind)
    | exact superpose eq693 eq4393
    | (have j0 := eq4393 (σ X0) X1
       have j1 := eq693 X0 X0 x
       grind)
    | exact resolve eq4393 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693 eq4393
  have eq21206 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (k X0 X0))) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq21188 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq21188 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq21188 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21188
  have eq21253 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | exact superpose eq4419 eq21206
    | (have j0 := eq21206 X0 X1
       have j1 := eq4419 X0 X1
       grind)
    | exact resolve eq21206 eq4419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4419 eq21206
  have eq106453 : ∀ X0 X1 : G, (k X0 (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq21253 (τ X0) X1
       grind)
    | exact superpose eq21253 eq17
    | (have j1 := eq21253 (τ X0) X1
       grind)
    | exact resolve eq17 eq21253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq21253
  have eq106598 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq106453 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq106453
    | (have j0 := eq106453 X0 X1
       grind)
    | exact resolve eq106453 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106453
  have eq106644 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq106598 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq106598
    | (have j0 := eq106598 X0 X1
       grind)
    | exact resolve eq106598 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106598
  have eq106938 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq106644 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106644
  have eq106939 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq106938 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106938
  have eq107086 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq921 X0 X1
       have i₂ := eq106939 X0
       grind)
    | exact superpose eq106939 eq921
    | (have j0 := eq921 X0 X1
       grind)
    | exact resolve eq921 eq106939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq107186 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq106939 (σ X0)
       grind)
    | exact superpose eq106939 eq15
    | exact resolve eq15 eq106939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107273 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq107186 X0
       have i₂ := eq106939 X0
       grind)
    | exact superpose eq106939 eq107186
    | exact resolve eq107186 eq106939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106939 eq107186
  have eq108216 : (σ y) = (M.op (M.op (σ (M.op y y)) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13866 (σ y)
       have i₂ := eq107273 y
       grind)
    | exact superpose eq107273 eq13866
    | exact resolve eq13866 eq107273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13866
  have eq108294 : (σ y) = (M.op (σ (M.op (M.op y y) x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108216
       have i₂ := eq14619 (M.op y y)
       grind)
    | exact superpose eq14619 eq108216
    | exact resolve eq108216 eq14619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14619 eq108216
  have eq268609 : (σ y) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13915
       have i₂ := eq107273 y
       grind)
    | exact superpose eq107273 eq13915
    | exact resolve eq13915 eq107273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13915
  have eq268642 : (M.op y y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq268609
       grind)
    | exact superpose eq268609 eq10
    | exact resolve eq10 eq268609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268609
  have eq268935 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq268642
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq268642
    | exact resolve eq268642 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268642
  have eq268962 : (M.op x y) = (τ (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq268935
       grind)
    | exact superpose eq268935 eq10
    | exact resolve eq10 eq268935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268935
  have eq269248 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq268962
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq268962
    | exact resolve eq268962 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268962
  have eq269253 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq269248
       grind)
    | exact superpose eq269248 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq269248
       grind)
    | exact resolve eq12 eq269248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269265 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq107086 y X0
       have i₂ := eq269248
       grind)
    | exact superpose eq269248 eq107086
    | (have j0 := eq107086 y X0
       grind)
    | exact resolve eq107086 eq269248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269248
  have eq269385 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq269265 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269265
  have eq269387 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq269253 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269253
  have eq270034 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k X0 y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq269385 (σ X0)
       grind)
    | exact superpose eq269385 eq15
    | exact resolve eq15 eq269385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269385
  have eq270146 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq269387 eq270034
    | exact resolve eq270034 eq269387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269387 eq270034
  have eq273933 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq270146 x
       grind)
    | exact superpose eq270146 eq16
    | (have r₁ := eq16
       have r₂ := eq270146 x
       grind)
    | exact resolve eq16 eq270146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270146
  have eq274125 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq273933
  have eq274504 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq274125 eq13856
    | exact resolve eq13856 eq274125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13856
  have eq274520 : x = (M.op (M.op y y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq62 y x
       have i₂ := eq274125
       grind)
    | exact superpose eq274125 eq62
    | exact resolve eq62 eq274125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq274125
  have eq277706 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq274520 eq108294
    | exact resolve eq108294 eq274520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108294 eq274520
  have eq277973 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13785 eq277706
    | exact resolve eq277706 eq13785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13785 eq277706
  have eq278020 : x = (M.op x y) := by
    first
    | (have r₁ := eq277973
       have r₂ := eq274504
       grind)
    | exact resolve eq277973 eq274504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274504 eq277973
  have eq278072 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq278020
       grind)
    | exact superpose eq278020 eq16
    | exact resolve eq16 eq278020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278083 : ∀ X0 : G, (M.op (M.op (M.op X0 y) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq278020
       grind)
    | exact superpose eq278020 eq9
    | exact resolve eq9 eq278020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278084 : x ≠ x ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq278020
       grind)
    | exact superpose eq278020 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq278020
       grind)
    | exact resolve eq13 eq278020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278147 : y = (k x y) ∨ y = (M.op y y) := by grind
  clear eq278084
  have eq279738 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq314 x y
       have i₂ := eq278147
       grind)
    | exact superpose eq278147 eq314
    | (have j0 := eq314 x y
       grind)
    | exact resolve eq314 eq278147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq279744 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq854 x y
       have i₂ := eq278147
       grind)
    | exact superpose eq278147 eq854
    | (have j0 := eq854 x y
       grind)
    | exact resolve eq854 eq278147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854 eq278147
  have eq279746 : (σ x) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq279744
       have r₂ := eq278072
       grind)
    | exact resolve eq279744 eq278072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279744
  have eq279748 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq279738
       have r₂ := eq278072
       grind)
    | exact resolve eq279738 eq278072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279738
  have eq282302 : x = (M.op (τ (M.op (σ y) (σ y))) x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq15500 (σ y) (σ x)
       have i₂ := eq279748
       grind)
    | exact superpose eq279748 eq15500
    | exact resolve eq15500 eq279748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15500 eq279748
  have eq282315 : x = (M.op (τ (σ (M.op y y))) x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq282302
       have i₂ := eq107273 y
       grind)
    | exact superpose eq107273 eq282302
    | exact resolve eq282302 eq107273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107273 eq282302
  have eq282356 : x = (M.op (M.op y y) x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq282315
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq282315
    | exact resolve eq282315 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282315
  have eq282417 : y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq278083 y
       have i₂ := eq282356
       grind)
    | exact superpose eq282356 eq278083
    | exact resolve eq278083 eq282356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278083 eq282356
  have eq282684 : y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq282417
       have i₂ := eq278020
       grind)
    | exact superpose eq278020 eq282417
    | exact resolve eq282417 eq278020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282417
  have eq282784 : (σ x) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq282684 eq279746
    | exact resolve eq279746 eq282684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279746 eq282684
  have eq282933 : y = (M.op y y) := by grind
  clear eq282784
  have eq282995 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq282933
       grind)
    | exact superpose eq282933 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq282933
       grind)
    | exact resolve eq12 eq282933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283009 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq107086 y X0
       have i₂ := eq282933
       grind)
    | exact superpose eq282933 eq107086
    | (have j0 := eq107086 y X0
       grind)
    | exact resolve eq107086 eq282933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107086 eq282933
  have eq283134 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq283009 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283009
  have eq283137 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq282995 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282995
  have eq283661 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq283134 (σ X0)
       grind)
    | exact superpose eq283134 eq15
    | exact resolve eq15 eq283134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283134
  have eq283777 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq283661 X0
       have i₂ := eq283137 X0
       grind)
    | exact superpose eq283137 eq283661
    | exact resolve eq283661 eq283137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283137 eq283661
  have eq284202 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq278072
       have i₂ := eq283777 x
       grind)
    | exact superpose eq283777 eq278072
    | exact resolve eq278072 eq283777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278072 eq283777
  have eq284636 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq284202
       have i₂ := eq278020
       grind)
    | exact superpose eq278020 eq284202
    | exact resolve eq284202 eq278020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278020 eq284202
  have eq284637 : False := by grind
  exact eq284637

/-- `Equation2683`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_x_pxy_Equation2683 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2683 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2683.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X0) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq20 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op X0 x) (M.op x x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (M.op X0 X0)
       have i₂ := eq20 X0 X0
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq41 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35
    | exact resolve eq35 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq69 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 (σ X0)) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq41
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq41 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq35
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq35 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (k X0 (σ X1)) (σ X2)
       have i₂ := eq34 X0 X1 X2
       grind)
    | exact superpose eq34 eq14
    | (have j0 := eq14 (k X0 (σ X1)) (σ X2)
       grind)
    | exact resolve eq14 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq242 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq68 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq68 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq68 X0 X1
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq25 (σ x)
       have i₂ := eq68 x x
       grind)
    | exact superpose eq68 eq25
    | (have j1 := eq68 X0 X0
       grind)
    | exact resolve eq25 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq68 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq246 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq245 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq248 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq243 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq249 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq242 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq252 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq249 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq249 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq249 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq333 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq246 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq246
    | (have j0 := eq246 (τ X0)
       grind)
    | exact resolve eq246 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq335 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq333 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq333
    | (have j0 := eq333 X0
       grind)
    | exact resolve eq333 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq338 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq335 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq335
    | (have j0 := eq335 X0
       grind)
    | exact resolve eq335 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq347 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (M.op X1 (σ (σ X0))) = (k X1 (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq252 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq252
    | (have j0 := eq252 (σ X0) X1
       grind)
    | exact resolve eq252 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq252 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq252
    | (have j0 := eq252 (τ X0) X1
       grind)
    | exact resolve eq252 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq350 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq350
    | (have j0 := eq350 X0 X1
       grind)
    | exact resolve eq350 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq355 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq352 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq352
    | (have j0 := eq352 X0 X1
       grind)
    | exact resolve eq352 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq361 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq355 (τ X0) X1
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq355
    | (have j0 := eq355 (τ X0) X1
       grind)
    | exact resolve eq355 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1581 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (σ (τ X0)) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq248 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq248
    | (have j0 := eq248 (τ X0)
       grind)
    | exact resolve eq248 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq1625 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1581 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1581
    | (have j0 := eq1581 X0
       grind)
    | exact resolve eq1581 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1581
  have eq1638 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1625 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1625
    | (have j0 := eq1625 X0
       grind)
    | exact resolve eq1625 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625
  have eq4545 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq69 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq4546 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq4545 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4545
  have eq4549 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4546 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4546
    | (have j0 := eq4546 X0
       grind)
    | exact resolve eq4546 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4546
  have eq4552 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4549 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4549
    | exact resolve eq4549 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4549
  have eq4607 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4552 X0
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq4552
    | (have j0 := eq4552 X0
       grind)
    | exact resolve eq4552 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4552
  have eq4684 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4607 X0
       grind)
    | exact superpose eq4607 eq11
    | (have j1 := eq4607 X0
       grind)
    | exact resolve eq11 eq4607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4607
  have eq4792 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4684 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4684
    | (have j0 := eq4684 X0
       grind)
    | exact resolve eq4684 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4684
  have eq4806 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4792 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq4792 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq4792 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4792
  have eq4811 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq252 X0 X1
       have i₂ := eq4806 X0
       grind)
    | exact superpose eq4806 eq252
    | (have j0 := eq252 X0 X1
       grind)
    | exact resolve eq252 eq4806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq4815 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (M.op X0 X0))) ∨ (M.op X1 (σ (σ X0))) = (k X1 (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq347 X0 X1
       have i₂ := eq4806 X0
       grind)
    | exact superpose eq4806 eq347
    | (have j0 := eq347 X0 X1
       grind)
    | exact resolve eq347 eq4806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq4817 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq361 X0 X1
       have i₂ := eq4806 X0
       grind)
    | exact superpose eq4806 eq361
    | (have j0 := eq361 X0 X1
       grind)
    | exact resolve eq361 eq4806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq4849 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4806 (σ X0)
       grind)
    | exact superpose eq4806 eq15
    | exact resolve eq15 eq4806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4856 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq47 X0 X0
       have i₂ := eq4806 (τ X0)
       grind)
    | exact superpose eq4806 eq47
    | exact resolve eq47 eq4806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4905 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4856 X0
       have i₂ := eq4806 X0
       grind)
    | exact superpose eq4806 eq4856
    | exact resolve eq4856 eq4806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4856
  have eq4912 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4849 X0
       have i₂ := eq4806 X0
       grind)
    | exact superpose eq4806 eq4849
    | exact resolve eq4849 eq4806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4849
  have eq5172 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq25 (τ X0)
       have i₂ := eq4905 X0
       grind)
    | exact superpose eq4905 eq25
    | exact resolve eq25 eq4905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq5184 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (τ X0) (τ X0)
       have i₂ := eq4905 X0
       grind)
    | exact superpose eq4905 eq20
    | exact resolve eq20 eq4905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5277 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0) (σ X0)
       have i₂ := eq4912 X0
       grind)
    | exact superpose eq4912 eq20
    | exact resolve eq20 eq4912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13443 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5172 (σ X1)
       have i₂ := eq72 X0 X1
       grind)
    | exact superpose eq72 eq5172
    | (have j1 := eq72 X1 X0
       grind)
    | exact resolve eq5172 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq5172
  have eq13538 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13443 X0 X1
       have i₂ := eq4905 (σ X0)
       grind)
    | exact superpose eq4905 eq13443
    | (have j0 := eq13443 X0 X1
       grind)
    | exact resolve eq13443 eq4905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13443
  have eq13562 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13538 X0 X1
       have i₂ := eq4912 X0
       grind)
    | exact superpose eq4912 eq13538
    | (have j0 := eq13538 X0 X1
       grind)
    | exact resolve eq13538 eq4912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13538
  have eq13573 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13562 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq13562
    | (have j0 := eq13562 X0 X1
       grind)
    | exact resolve eq13562 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13562
  have eq13578 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13573 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13573
    | (have j0 := eq13573 X0 X1
       grind)
    | exact resolve eq13573 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13573
  have eq33863 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (k (σ X0) (σ X0)) (σ X0)) = (σ (k (k (τ (σ X0)) X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1638 (σ X0)
       have i₂ := eq216 (σ X0) X0 X0
       grind)
    | exact superpose eq216 eq1638
    | (have j0 := eq1638 (σ X0)
       have j1 := eq216 (σ X0) X0 X0
       grind)
    | exact resolve eq1638 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq1638
  have eq33916 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (k (σ X0) (σ X0)) (σ X0)) = (σ (k (k (τ (σ X0)) X0) X0)) := by
    intro X0
    first
    | (have j0 := eq33863 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33863
  have eq33969 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (k (σ X0) (σ X0)) (σ X0)) = (σ (k (k (τ (σ X0)) X0) X0)) := by
    intro X0
    first
    | (have j0 := eq33916 X0
       have j1 := eq338 (σ X0)
       grind)
    | (have r₁ := eq33916 X0
       have r₂ := eq338 (σ X0)
       grind)
    | exact resolve eq33916 eq338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338 eq33916
  have eq34062 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (k (σ X0) (σ X0)) (σ X0)) = (σ (k (k (τ (σ X0)) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq33969 X0
       have i₂ := eq4912 X0
       grind)
    | exact superpose eq4912 eq33969
    | (have j0 := eq33969 X0
       grind)
    | exact resolve eq33969 eq4912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33969
  have eq34080 : ∀ X0 : G, (M.op (k (σ X0) (σ X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34062 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34062
    | (have j0 := eq34062 X0
       grind)
    | exact resolve eq34062 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34062
  have eq34091 : ∀ X0 : G, (M.op (k (σ X0) (σ X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34080 X0
       have i₂ := eq4806 X0
       grind)
    | exact superpose eq4806 eq34080
    | (have j0 := eq34080 X0
       grind)
    | exact resolve eq34080 eq4806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34080
  have eq34099 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34091 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq34091
    | (have j0 := eq34091 X0
       grind)
    | exact resolve eq34091 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34091
  have eq34105 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34099 X0
       have i₂ := eq4806 X0
       grind)
    | exact superpose eq4806 eq34099
    | (have j0 := eq34099 X0
       grind)
    | exact resolve eq34099 eq4806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4806 eq34099
  have eq34123 : ∀ X0 : G, (M.op (σ (M.op (τ X0) (τ X0))) X0) = (σ (k (M.op (τ X0) (τ X0)) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq34105 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34105
    | exact resolve eq34105 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34105
  have eq34268 : ∀ X0 : G, (M.op (σ (M.op (τ X0) (τ X0))) X0) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq34123 X0
       have i₂ := eq18 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq18 eq34123
    | (have j0 := eq34123 X0
       grind)
    | exact resolve eq34123 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34123
  have eq34307 : ∀ X0 : G, (M.op (σ (τ (M.op X0 X0))) X0) = (k (σ (τ (M.op X0 X0))) X0) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq34268 X0
       have i₂ := eq4905 X0
       grind)
    | exact superpose eq4905 eq34268
    | (have j0 := eq34268 X0
       grind)
    | exact resolve eq34268 eq4905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34268
  have eq34322 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq34307 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq34307
    | (have j0 := eq34307 X0
       grind)
    | exact resolve eq34307 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34307
  have eq34333 : ∀ X0 : G, (σ (τ (M.op X0 X0))) = X0 ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq34322 X0
       have i₂ := eq4905 X0
       grind)
    | exact superpose eq4905 eq34322
    | (have j0 := eq34322 X0
       grind)
    | exact resolve eq34322 eq4905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34322
  have eq34341 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq34333 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq34333
    | (have j0 := eq34333 X0
       grind)
    | exact resolve eq34333 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34333
  have eq34347 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq34341 X0
       have j1 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq34341 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq34341 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34341
  have eq34374 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq34347 (σ X0)
       have i₂ := eq4912 X0
       grind)
    | exact superpose eq4912 eq34347
    | exact resolve eq34347 eq4912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34376 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq34347 (τ X0)
       have i₂ := eq4905 X0
       grind)
    | exact superpose eq4905 eq34347
    | exact resolve eq34347 eq4905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34499 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq34376 X0
       have i₂ := eq47 X0 (M.op X0 X0)
       grind)
    | exact superpose eq47 eq34376
    | exact resolve eq34376 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34376
  have eq34501 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq34374 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq34374
    | exact resolve eq34374 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34374
  have eq34543 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq34499 X0
       have i₂ := eq34347 X0
       grind)
    | exact superpose eq34347 eq34499
    | exact resolve eq34499 eq34347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34499
  have eq34545 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq34501 X0
       have i₂ := eq34347 X0
       grind)
    | exact superpose eq34347 eq34501
    | exact resolve eq34501 eq34347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34347 eq34501
  have eq36185 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5277 X0
       have i₂ := eq34545 X0
       grind)
    | exact superpose eq34545 eq5277
    | exact resolve eq5277 eq34545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5277
  have eq36357 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (M.op (σ (M.op X0 X0)) (σ X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq36185 (σ X0)
       have i₂ := eq4912 X0
       grind)
    | exact superpose eq4912 eq36185
    | exact resolve eq36185 eq4912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36526 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (σ (M.op (M.op X0 X0) X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq36357 X0
       have i₂ := eq34545 X0
       grind)
    | exact superpose eq34545 eq36357
    | exact resolve eq36357 eq34545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36357
  have eq81500 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 (σ X1))
       have i₂ := eq13578 X1 X0
       grind)
    | exact superpose eq13578 eq11
    | (have j1 := eq13578 X1 X0
       grind)
    | exact resolve eq11 eq13578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13578
  have eq81662 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81500 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq81500
    | (have j0 := eq81500 X0 X1
       grind)
    | exact resolve eq81500 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81500
  have eq83194 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq81662 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81662
    | (have j0 := eq81662 X0 (τ X0)
       grind)
    | exact resolve eq81662 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81662
  have eq83401 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83194 X0 X1
       have i₂ := eq4905 X0
       grind)
    | exact superpose eq4905 eq83194
    | (have j0 := eq83194 X0 X1
       grind)
    | exact resolve eq83194 eq4905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83194
  have eq83452 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5184 X0
       have i₂ := eq83401 X0 X1
       grind)
    | exact superpose eq83401 eq5184
    | (have j1 := eq83401 X0 X1
       grind)
    | exact resolve eq5184 eq83401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5184 eq83401
  have eq83741 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83452 X0 X1
       have i₂ := eq4905 X0
       grind)
    | exact superpose eq4905 eq83452
    | (have j0 := eq83452 X0 X1
       grind)
    | exact resolve eq83452 eq4905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83452
  have eq83763 : ∀ X0 X1 : G, (τ X0) = (τ (M.op (M.op X0 X0) X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83741 X0 X1
       have i₂ := eq34543 X0
       grind)
    | exact superpose eq34543 eq83741
    | (have j0 := eq83741 X0 X1
       grind)
    | exact resolve eq83741 eq34543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83741
  have eq85958 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op X0 X0) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (M.op X0 X0) X0)
       have i₂ := eq83763 X0 X1
       grind)
    | exact superpose eq83763 eq11
    | (have j1 := eq83763 X0 X1
       grind)
    | exact resolve eq11 eq83763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83763
  have eq86180 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq85958 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq85958
    | (have j0 := eq85958 X0 X1
       grind)
    | exact resolve eq85958 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85958
  have eq86598 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq36185 X0
       have i₂ := eq86180 X0 X1
       grind)
    | exact superpose eq86180 eq36185
    | (have j1 := eq86180 X0 X1
       grind)
    | exact resolve eq36185 eq86180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36185
  have eq86832 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq86598 X0 X1
       have i₂ := eq4912 X0
       grind)
    | exact superpose eq4912 eq86598
    | (have j0 := eq86598 X0 X1
       grind)
    | exact resolve eq86598 eq4912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86598
  have eq86953 : ∀ X0 X1 X2 : G, (σ (σ X0)) ≠ (σ (σ X0)) ∨ (M.op X1 (σ (σ X0))) = (k X1 (σ (σ X0))) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4815 X0 X1
       have i₂ := eq86832 X0 X2
       grind)
    | exact superpose eq86832 eq4815
    | (have j0 := eq4815 X0 X1
       have j1 := eq86832 X0 X2
       grind)
    | exact resolve eq4815 eq86832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4815 eq86832
  have eq87135 : ∀ X0 X1 X2 : G, (M.op X1 (σ (σ X0))) = (k X1 (σ (σ X0))) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq86953 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86953
  have eq211670 : ∀ X0 X1 X2 : G, (k X0 (τ (σ (σ X1)))) = (τ (M.op (σ X0) (σ (σ X1)))) ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X1 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41 X0 (σ (σ X1))
       have i₂ := eq87135 X1 (σ X0) X2
       grind)
    | exact superpose eq87135 eq41
    | (have j1 := eq87135 X1 X1 X2
       grind)
    | exact resolve eq41 eq87135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq87135
  have eq211770 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (τ (M.op (σ X0) (σ (σ X1)))) ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X1 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq211670 X0 X1 X2
       have i₂ := eq10 (σ X1)
       grind)
    | exact superpose eq10 eq211670
    | (have j0 := eq211670 X0 X1 X2
       grind)
    | exact resolve eq211670 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211670
  have eq298379 : ∀ X0 X1 : G, (τ (σ (σ X0))) = (k (σ (M.op (M.op X0 X0) X0)) (σ X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq211770 (σ (M.op (M.op X0 X0) X0)) X0 X1
       have i₂ := eq36526 X0
       grind)
    | exact superpose eq36526 eq211770
    | (have j0 := eq211770 X0 X0 X1
       grind)
    | exact resolve eq211770 eq36526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36526 eq211770
  have eq298884 : ∀ X0 X1 : G, (τ (σ (σ X0))) = (σ (k (M.op (M.op X0 X0) X0) X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq298379 X0 X1
       have i₂ := eq15 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq15 eq298379
    | (have j0 := eq298379 X0 X1
       grind)
    | exact resolve eq298379 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298379
  have eq299053 : ∀ X0 X1 : G, (σ X0) = (σ (k (M.op (M.op X0 X0) X0) X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq298884 X0 X1
       have i₂ := eq10 (σ X0)
       grind)
    | exact superpose eq10 eq298884
    | (have j0 := eq298884 X0 X1
       grind)
    | exact resolve eq298884 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298884
  have eq300458 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (M.op X0 X0) X0) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (M.op (M.op X0 X0) X0) X0)
       have i₂ := eq299053 X0 X1
       grind)
    | exact superpose eq299053 eq10
    | (have j1 := eq299053 X0 X1
       grind)
    | exact resolve eq10 eq299053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299053
  have eq300888 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) X0) X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq300458 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq300458
    | (have j0 := eq300458 X0 X1
       grind)
    | exact resolve eq300458 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300458
  have eq301299 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) ≠ X0 ∨ (M.op (M.op (M.op X0 X0) X0) X0) = (k (M.op (M.op X0 X0) X0) X0) ∨ (M.op X0 (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq300888 X0 (M.op (M.op X0 X0) X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300888
  have eq301301 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = (k (M.op (M.op X0 X0) X0) X0) ∨ (M.op X0 (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq301299 X0
       grind)
    | (have r₁ := eq301299 X0
       have r₂ := eq20 X0 X0
       grind)
    | exact resolve eq301299 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301299
  have eq301381 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) X0) = X0 ∨ (M.op X0 (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq301301 X0
       have i₂ := eq20 X0 X0
       grind)
    | exact superpose eq20 eq301301
    | (have j0 := eq301301 X0
       grind)
    | exact resolve eq301301 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301301
  have eq302266 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (M.op (τ X0) (τ X0)) (τ X0))
       have i₂ := eq301381 (τ X0)
       grind)
    | exact superpose eq301381 eq18
    | (have j1 := eq301381 (τ X0)
       grind)
    | exact resolve eq18 eq301381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq301381
  have eq302413 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ (M.op X0 X0)) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq302266 X0
       have i₂ := eq4905 X0
       grind)
    | exact superpose eq4905 eq302266
    | (have j0 := eq302266 X0
       grind)
    | exact resolve eq302266 eq4905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302266
  have eq302538 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ (M.op (M.op X0 X0) X0))) X0) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq302413 X0
       have i₂ := eq34543 X0
       grind)
    | exact superpose eq34543 eq302413
    | (have j0 := eq302413 X0
       grind)
    | exact resolve eq302413 eq34543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302413
  have eq302617 : ∀ X0 : G, (σ (τ X0)) = (k (M.op (M.op X0 X0) X0) X0) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq302538 X0
       have i₂ := eq11 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq11 eq302538
    | (have j0 := eq302538 X0
       grind)
    | exact resolve eq302538 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302538
  have eq302691 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq302617 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq302617
    | (have j0 := eq302617 X0
       grind)
    | exact resolve eq302617 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302617
  have eq302746 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (k (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq302691 X0
       have i₂ := eq4905 X0
       grind)
    | exact superpose eq4905 eq302691
    | (have j0 := eq302691 X0
       grind)
    | exact resolve eq302691 eq4905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302691
  have eq302791 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X0) X0))) ∨ (k (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq302746 X0
       have i₂ := eq34543 X0
       grind)
    | exact superpose eq34543 eq302746
    | (have j0 := eq302746 X0
       grind)
    | exact resolve eq302746 eq34543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302746
  have eq302919 : ∀ X0 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (M.op (σ (M.op X0 X0)) (σ X0)))) ∨ (σ X0) = (k (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq302791 (σ X0)
       have i₂ := eq4912 X0
       grind)
    | exact superpose eq4912 eq302791
    | exact resolve eq302791 eq4912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302791
  have eq303226 : ∀ X0 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ (M.op (M.op X0 X0) X0)))) ∨ (σ X0) = (k (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq302919 X0
       have i₂ := eq34545 X0
       grind)
    | exact superpose eq34545 eq302919
    | (have j0 := eq302919 X0
       grind)
    | exact resolve eq302919 eq34545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302919
  have eq303353 : ∀ X0 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (M.op (M.op X0 X0) X0)) ∨ (σ X0) = (k (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq303226 X0
       have i₂ := eq10 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq10 eq303226
    | (have j0 := eq303226 X0
       grind)
    | exact resolve eq303226 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303226
  have eq303435 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = X0 ∨ (σ X0) = (k (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq303353 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq303353
    | (have j0 := eq303353 X0
       grind)
    | exact resolve eq303353 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303353
  have eq303502 : ∀ X0 : G, (σ X0) = (k (σ (M.op (M.op X0 X0) X0)) (σ X0)) ∨ (M.op X0 (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq303435 X0
       have i₂ := eq34545 X0
       grind)
    | exact superpose eq34545 eq303435
    | (have j0 := eq303435 X0
       grind)
    | exact resolve eq303435 eq34545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303435
  have eq303557 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = X0 ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq303502 X0
       have i₂ := eq15 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq15 eq303502
    | (have j0 := eq303502 X0
       grind)
    | exact resolve eq303502 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303502
  have eq304691 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X0)) X0) = X0 ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (M.op (M.op X0 X0) X0) X0
       have i₂ := eq303557 X0
       grind)
    | exact superpose eq303557 eq20
    | (have j1 := eq303557 X0
       grind)
    | exact resolve eq20 eq303557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq307891 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) X0) X0)) ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq304691 X0
       have i₂ := eq303557 X0
       grind)
    | exact superpose eq303557 eq304691
    | (have j0 := eq304691 X0
       have j1 := eq303557 X0
       grind)
    | exact resolve eq304691 eq303557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303557 eq304691
  have eq308171 : ∀ X0 : G, (σ X0) = (σ (k (M.op (M.op X0 X0) X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq307891 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307891
  have eq309868 : ∀ X0 : G, (τ (σ X0)) = (k (M.op (M.op X0 X0) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k (M.op (M.op X0 X0) X0) X0)
       have i₂ := eq308171 X0
       grind)
    | exact superpose eq308171 eq10
    | (have j1 := eq308171 X0
       grind)
    | exact resolve eq10 eq308171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308171
  have eq310315 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq309868 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq309868
    | (have j0 := eq309868 X0
       grind)
    | exact resolve eq309868 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309868
  have eq310494 : ∀ X0 : G, (τ X0) = (k (M.op (τ (M.op X0 X0)) (τ X0)) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq310315 (τ X0)
       have i₂ := eq4905 X0
       grind)
    | exact superpose eq4905 eq310315
    | exact resolve eq310315 eq4905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4905 eq310315
  have eq310823 : ∀ X0 : G, (τ X0) = (k (τ (M.op (M.op X0 X0) X0)) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq310494 X0
       have i₂ := eq34543 X0
       grind)
    | exact superpose eq34543 eq310494
    | (have j0 := eq310494 X0
       grind)
    | exact resolve eq310494 eq34543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34543 eq310494
  have eq310884 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (k (M.op (M.op X0 X0) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq310823 X0
       have i₂ := eq47 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq47 eq310823
    | (have j0 := eq310823 X0
       grind)
    | exact resolve eq310823 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq310823
  have eq314259 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (τ X0) = (τ (k (M.op (M.op X0 X0) X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4817 X0 X1
       have i₂ := eq310884 X0
       grind)
    | exact superpose eq310884 eq4817
    | (have j0 := eq4817 X0 X1
       have j1 := eq310884 X0
       grind)
    | (have r₁ := eq4817 X0 X1
       have r₂ := eq310884 X0
       grind)
    | exact resolve eq4817 eq310884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4817 eq310884
  have eq314530 : ∀ X0 X1 : G, (τ X0) = (τ (k (M.op (M.op X0 X0) X0) X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq314259 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314259
  have eq340164 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) X0) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (M.op (M.op (σ X0) (σ X0)) (σ X0)) X0
       have i₂ := eq314530 (σ X0) X1
       grind)
    | exact superpose eq314530 eq35
    | (have j1 := eq314530 (σ X0) X1
       grind)
    | exact resolve eq35 eq314530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq314530
  have eq340469 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (σ (M.op X0 X0)) (σ X0))) X0) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq340164 X0 X1
       have i₂ := eq4912 X0
       grind)
    | exact superpose eq4912 eq340164
    | (have j0 := eq340164 X0 X1
       grind)
    | exact resolve eq340164 eq4912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340164
  have eq340539 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ (M.op (M.op X0 X0) X0))) X0) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq340469 X0 X1
       have i₂ := eq34545 X0
       grind)
    | exact superpose eq34545 eq340469
    | (have j0 := eq340469 X0 X1
       grind)
    | exact resolve eq340469 eq34545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34545 eq340469
  have eq340596 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (M.op X0 X0) X0) X0) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq340539 X0 X1
       have i₂ := eq10 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq10 eq340539
    | (have j0 := eq340539 X0 X1
       grind)
    | exact resolve eq340539 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340539
  have eq340638 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) X0) X0) = X0 ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq340596 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq340596
    | (have j0 := eq340596 X0 X1
       grind)
    | exact resolve eq340596 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340596
  have eq340676 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) X0) X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq340638 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq340638
    | (have j0 := eq340638 X0 X1
       grind)
    | exact resolve eq340638 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340638
  have eq341019 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) ≠ X0 ∨ (M.op (M.op (M.op X0 X0) X0) X0) = (k (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have j0 := eq340676 X0 (M.op (M.op X0 X0) X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340676
  have eq341021 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = (k (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have j0 := eq341019 X0
       grind)
    | (have r₁ := eq341019 X0
       have r₂ := eq20 X0 X0
       grind)
    | exact resolve eq341019 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341019
  have eq341135 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq341021 X0
       have i₂ := eq20 X0 X0
       grind)
    | exact superpose eq20 eq341021
    | exact resolve eq341021 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341021
  have eq342370 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq341135 X0
       have i₂ := eq86180 X0 X1
       grind)
    | exact superpose eq86180 eq341135
    | (have j1 := eq86180 X0 X1
       grind)
    | exact resolve eq341135 eq86180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86180 eq341135
  have eq342692 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq342370 X0 X1
       have j1 := eq355 X0 X1
       grind)
    | (have r₁ := eq342370 X0 X1
       have r₂ := eq355 X0 X1
       grind)
    | exact resolve eq342370 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq342370
  have eq343342 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq342692 (σ X1) (σ X0)
       grind)
    | exact superpose eq342692 eq15
    | (have j1 := eq342692 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq342692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343355 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq342692 X1 (τ X0)
       grind)
    | exact superpose eq342692 eq17
    | (have j1 := eq342692 X1 (τ X0)
       grind)
    | exact resolve eq17 eq342692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq342692
  have eq347240 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq343355 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq343355
    | exact resolve eq343355 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343355
  have eq347968 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq347240 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq347240
    | (have j0 := eq347240 X0 X1
       grind)
    | exact resolve eq347240 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347240
  have eq355163 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq343342 x y
       grind)
    | exact superpose eq343342 eq16
    | (have j1 := eq343342 x y
       grind)
    | exact resolve eq16 eq343342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343342
  have eq358631 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq355163
       have i₂ := eq347968 x y
       grind)
    | exact superpose eq347968 eq355163
    | (have j1 := eq347968 (σ x) (σ y)
       grind)
    | (have r₁ := eq355163
       have r₂ := eq347968 x y
       grind)
    | exact resolve eq355163 eq347968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347968 eq355163
  have eq358636 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq358631
  have eq358662 : y = (M.op (M.op y x) y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq20 x y
       have i₂ := eq358636
       grind)
    | exact superpose eq358636 eq20
    | exact resolve eq20 eq358636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360687 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq358662
       have i₂ := eq358636
       grind)
    | exact superpose eq358636 eq358662
    | exact resolve eq358662 eq358636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358636 eq358662
  have eq360812 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq360687
  have eq360889 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq20 (σ x) (σ y)
       have i₂ := eq360812
       grind)
    | exact superpose eq360812 eq20
    | exact resolve eq20 eq360812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq363448 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq360889
       have i₂ := eq360812
       grind)
    | exact superpose eq360812 eq360889
    | exact resolve eq360889 eq360812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360812 eq360889
  have eq363620 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq363448
  have eq363666 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq363620
       have i₂ := eq4912 y
       grind)
    | exact superpose eq4912 eq363620
    | exact resolve eq363620 eq4912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4912 eq363620
  have eq365630 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq363666
       grind)
    | exact superpose eq363666 eq10
    | exact resolve eq10 eq363666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363666
  have eq366124 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq365630
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq365630
    | exact resolve eq365630 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365630
  have eq366125 : y = (M.op y y) := by grind
  clear eq366124
  have eq366178 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq366125
       grind)
    | exact superpose eq366125 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq366125
       grind)
    | exact resolve eq12 eq366125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366205 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4811 y X0
       have i₂ := eq366125
       grind)
    | exact superpose eq366125 eq4811
    | (have j0 := eq4811 y X0
       grind)
    | exact resolve eq4811 eq366125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4811 eq366125
  have eq366522 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq366205 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366205
  have eq366525 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq366178 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366178
  have eq372270 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq366522 (σ X0)
       grind)
    | exact superpose eq366522 eq15
    | exact resolve eq15 eq366522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366522
  have eq372430 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq372270 X0
       have i₂ := eq366525 X0
       grind)
    | exact superpose eq366525 eq372270
    | exact resolve eq372270 eq366525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366525 eq372270
  have eq378347 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq372430 x
       grind)
    | exact superpose eq372430 eq16
    | (have r₁ := eq16
       have r₂ := eq372430 x
       grind)
    | exact resolve eq16 eq372430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372430
  have eq378913 : False := by grind
  exact eq378913
