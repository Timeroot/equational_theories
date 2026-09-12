import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_y_pxy_Equation422 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0)))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq282
  have eq346 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq347 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq348 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  clear eq346
  have eq384 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
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
  have eq388 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq348 y (σ x)
       grind)
    | exact superpose eq348 eq16
    | (have j1 := eq348 y (σ x)
       grind)
    | exact resolve eq16 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq398 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq388
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq388
    | exact resolve eq388 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq407 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq384 X1 X0
       grind)
    | exact superpose eq384 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq384 X1 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq384 X0 X1
       grind)
    | exact resolve eq13 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X2 X0))) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X0
       have i₂ := eq384 X1 X0
       grind)
    | exact superpose eq384 eq9
    | (have j1 := eq384 (M.op X1 (M.op X2 X0)) X1
       grind)
    | exact resolve eq9 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq407 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq415 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq413 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq413 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq413 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq442 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq415 (τ X0) X1
       grind)
    | exact superpose eq415 eq17
    | (have j1 := eq415 (τ X0) X1
       grind)
    | exact resolve eq17 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq448 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq415 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq601 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X1 (M.op X2 X0)) X0) = (k (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq408 (M.op X1 (M.op X2 X0)) X0 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq408
    | (have j0 := eq408 (M.op X1 (M.op X2 X0)) X0 X2
       grind)
    | exact resolve eq408 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (k (M.op X1 X2) X0) = (M.op (M.op X1 X2) X0) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq408 (M.op X1 X2) X0 X0
       have i₂ := eq408 X2 X0 X1
       grind)
    | exact superpose eq408 eq408
    | (have j0 := eq408 (M.op X1 X2) X0 X2
       have j1 := eq408 (M.op X1 X2) X0 X2
       grind)
    | exact resolve eq408 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) ∨ (M.op X2 (M.op X0 (M.op X1 X2))) = (k X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq408 X2 (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))
       have i₂ := eq62 X2 X0 X1
       grind)
    | exact superpose eq62 eq408
    | (have j0 := eq408 X2 (M.op X0 (M.op X1 X2)) X2
       grind)
    | exact resolve eq408 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq408
  have eq618 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X2))) = (k X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq605 X0 X1 X2
       have j1 := eq12 X2 (M.op X0 (M.op X1 X2))
       grind)
    | (have r₁ := eq605 X0 X1 X2
       have r₂ := eq12 X0 (M.op X0 (M.op X1 X2))
       grind)
    | exact resolve eq605 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq620 : ∀ X0 X1 X2 : G, (k (M.op X1 X2) X0) = (M.op (M.op X1 X2) X0) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq602 X0 X1 X2
       have j1 := eq12 (M.op X1 X2) X0
       grind)
    | (have r₁ := eq602 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq602 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq621 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) X0) = (k (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq601 X0 X1 X2
       have j1 := eq12 (M.op X1 (M.op X2 X0)) X0
       grind)
    | (have r₁ := eq601 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq601 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq644 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X2 (σ X0))))) = (τ (M.op (σ X0) (M.op X1 (M.op X2 (σ X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X0 (M.op X1 (M.op X2 (σ X0)))
       have i₂ := eq618 X1 X2 (σ X0)
       grind)
    | exact superpose eq618 eq28
    | exact resolve eq28 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq662 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (k X0 (M.op X1 X2)) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq621 X0 X1 X2
       have i₂ := eq384 (M.op X2 X0) X1
       grind)
    | exact superpose eq384 eq621
    | (have j1 := eq384 (M.op X1 X2) X0
       grind)
    | exact resolve eq621 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq769 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq442 X1 (τ X0)
       grind)
    | exact superpose eq442 eq18
    | (have j1 := eq442 X1 (τ X0)
       grind)
    | exact resolve eq18 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq442
  have eq774 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq769 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq769
    | (have j0 := eq769 X0 X1
       grind)
    | exact resolve eq769 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq787 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq774 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq774
    | (have j0 := eq774 X0 X1
       grind)
    | exact resolve eq774 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq790 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq787 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq787
    | (have j0 := eq787 X0 X1
       grind)
    | exact resolve eq787 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq847 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq790 X1 X0
       have i₂ := eq415 X0 X1
       grind)
    | exact superpose eq415 eq790
    | (have j0 := eq790 X1 X0
       have j1 := eq415 X0 X1
       grind)
    | exact resolve eq790 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq851 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X0)) (τ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq790 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq790
    | exact resolve eq790 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq910 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op (τ (σ X0)) X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq851 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq851
    | (have j0 := eq851 X0 X1
       grind)
    | exact resolve eq851 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq912 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq847 X0 X1
       have j1 := eq448 X0 X1
       grind)
    | (have r₁ := eq847 X0 X1
       have r₂ := eq448 X0 X1
       grind)
    | exact resolve eq847 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448 eq847
  have eq931 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq910 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq910
    | (have j0 := eq910 X0 X1
       grind)
    | exact resolve eq910 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq955 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq912 X1 (σ X0)
       grind)
    | exact superpose eq912 eq22
    | (have j1 := eq912 X1 (σ X0)
       grind)
    | exact resolve eq22 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq989 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq955 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq955
    | (have j0 := eq955 X0 X1
       grind)
    | exact resolve eq955 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq1008 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq989 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq989
    | (have j0 := eq989 X0 X1
       grind)
    | exact resolve eq989 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq1050 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq931 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq1252 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1008 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1008
    | exact resolve eq1008 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1319 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1252 x y
       grind)
    | exact superpose eq1252 eq16
    | (have j1 := eq1252 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1252 x y
       grind)
    | exact resolve eq16 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252
  have eq1338 : y = (k x y) := by grind
  clear eq1319
  have eq1513 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq398
       have i₂ := eq384 y x
       grind)
    | exact superpose eq384 eq398
    | (have j1 := eq384 y x
       grind)
    | exact resolve eq398 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384 eq398
  have eq1514 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq1513
  have eq1515 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1514
       have i₂ := eq1338
       grind)
    | exact superpose eq1338 eq1514
    | exact resolve eq1514 eq1338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1514
  have eq1516 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1515
       have i₂ := eq1338
       grind)
    | exact superpose eq1338 eq1515
    | exact resolve eq1515 eq1338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1515
  have eq1519 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y (M.op y (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 x
       have i₂ := eq1516
       grind)
    | exact superpose eq1516 eq9
    | exact resolve eq9 eq1516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3052 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ y = (M.op y (M.op y (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq662 X0 (σ x) (σ y)
       have i₂ := eq1519 X0
       grind)
    | exact superpose eq1519 eq662
    | (have j0 := eq662 X0 X1 (σ y)
       have j1 := eq1519 X1
       grind)
    | exact resolve eq662 eq1519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1519
  have eq3059 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ (M.op X0 y) = (k X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq662 X0 x y
       have i₂ := eq1516
       grind)
    | exact superpose eq1516 eq662
    | (have j0 := eq662 X0 x y
       grind)
    | exact resolve eq662 eq1516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516
  have eq3078 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq3059 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3059
  have eq3079 : ∀ X0 X1 : G, y = (M.op y (M.op y (M.op X1 y))) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq3052 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3052
  have eq3109 : ∀ X0 X1 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ (k (σ y) X0) = (M.op (σ y) X0) ∨ (M.op X1 y) = (k X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq620 X0 (σ x) (σ y)
       have i₂ := eq3078 X0
       grind)
    | exact superpose eq3078 eq620
    | (have j0 := eq620 X0 X1 (σ y)
       have j1 := eq3078 X1
       grind)
    | exact resolve eq620 eq3078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620 eq3078
  have eq3115 : ∀ X0 X1 : G, (M.op X1 y) = (k X1 y) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0 X1
    first
    | (have j0 := eq3109 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3109
  have eq3612 : ∀ X0 : G, y = (M.op x y) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq1338
       have i₂ := eq3115 X0 x
       grind)
    | exact superpose eq3115 eq1338
    | (have j1 := eq3115 X0 x
       grind)
    | exact resolve eq1338 eq3115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3115
  have eq6387 : ∀ X1 : G, y = (M.op y y) ∨ (M.op X1 (σ y)) = (k X1 (σ y)) := by
    intro X1
    first
    | (have i₁ := eq9 y y x
       have i₂ := eq3079 X1 x
       grind)
    | exact superpose eq3079 eq9
    | (have j1 := eq3079 X1 X1
       grind)
    | exact resolve eq9 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3079
  have eq6438 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (σ (k y y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1050 y y
       have i₂ := eq6387 X0
       grind)
    | exact superpose eq6387 eq1050
    | (have j0 := eq1050 y y
       have j1 := eq6387 X0
       grind)
    | exact resolve eq1050 eq6387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050 eq6387
  have eq6439 : ∀ X0 : G, (σ y) = (σ (k y y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq6438 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6438
  have eq6446 : ∀ X0 : G, (σ y) = (σ (M.op y y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6439 X0
       have i₂ := eq271 y
       grind)
    | exact superpose eq271 eq6439
    | (have j0 := eq6439 X0
       grind)
    | exact resolve eq6439 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6439
  have eq6448 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq6446 X0
       have j1 := eq347 y X0
       grind)
    | (have r₁ := eq6446 X0
       have r₂ := eq347 y x
       grind)
    | exact resolve eq6446 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347 eq6446
  have eq6466 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq22 X0 y
       have i₂ := eq6448 X0
       grind)
    | exact superpose eq6448 eq22
    | exact resolve eq22 eq6448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq6482 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq6448 (σ X0)
       grind)
    | exact superpose eq6448 eq15
    | exact resolve eq15 eq6448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6448
  have eq6665 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6482 x
       grind)
    | exact superpose eq6482 eq16
    | exact resolve eq16 eq6482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6482
  have eq6716 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq6665
       have i₂ := eq1338
       grind)
    | exact superpose eq1338 eq6665
    | exact resolve eq6665 eq1338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6665
  have eq6739 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq6716
       have i₂ := eq3612 X0
       grind)
    | exact superpose eq3612 eq6716
    | (have j1 := eq3612 X0
       grind)
    | exact resolve eq6716 eq3612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3612
  have eq6745 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq6739 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6739
  have eq6768 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq28 y X0
       have i₂ := eq6745 X0
       grind)
    | exact superpose eq6745 eq28
    | exact resolve eq28 eq6745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq6745
  have eq6866 : ∀ X0 X1 : G, (τ (σ y)) = (k y (τ (M.op (σ y) (M.op X0 (M.op X1 (σ y)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq6768 (M.op (σ y) (M.op X0 (M.op X1 (σ y))))
       have i₂ := eq9 (σ y) X0 X1
       grind)
    | exact superpose eq9 eq6768
    | exact resolve eq6768 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6928 : ∀ X0 X1 : G, (τ (σ y)) = (k y (k y (τ (M.op X0 (M.op X1 (σ y)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq6866 X0 X1
       have i₂ := eq644 y X0 X1
       grind)
    | exact superpose eq644 eq6866
    | exact resolve eq6866 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644 eq6866
  have eq6943 : ∀ X0 X1 : G, y = (k y (k y (τ (M.op X0 (M.op X1 (σ y)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq6928 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq6928
    | exact resolve eq6928 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6928
  have eq7288 : ∀ X0 : G, y = (k y (k y (k y (τ (M.op X0 (σ y)))))) := by
    intro X0
    first
    | (have i₁ := eq6943 (σ y) X0
       have i₂ := eq6768 (M.op X0 (σ y))
       grind)
    | exact superpose eq6768 eq6943
    | exact resolve eq6943 eq6768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6768 eq6943
  have eq7338 : ∀ X0 : G, y = (k y (k y (k y (k (τ X0) y)))) := by
    intro X0
    first
    | (have i₁ := eq7288 X0
       have i₂ := eq6466 X0
       grind)
    | exact superpose eq6466 eq7288
    | exact resolve eq7288 eq6466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6466 eq7288
  have eq7351 : ∀ X0 : G, y = (k y (k y (k y (k X0 y)))) := by
    intro X0
    first
    | (have i₁ := eq7338 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7338
    | exact resolve eq7338 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7338
  have eq7445 : y = (k y (k y (k y (M.op y y)))) := by
    first
    | (have i₁ := eq7351 y
       have i₂ := eq271 y
       grind)
    | exact superpose eq271 eq7351
    | exact resolve eq7351 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7459 : y = (k y (k y (k y y))) := by
    first
    | (have i₁ := eq7351 x
       have i₂ := eq1338
       grind)
    | exact superpose eq1338 eq7351
    | exact resolve eq7351 eq1338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7351
  have eq7511 : y = (k y (k y (M.op y y))) := by
    first
    | (have i₁ := eq7459
       have i₂ := eq271 y
       grind)
    | exact superpose eq271 eq7459
    | exact resolve eq7459 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7459
  have eq7585 : y = (k y y) := by
    first
    | (have i₁ := eq7445
       have i₂ := eq7511
       grind)
    | exact superpose eq7511 eq7445
    | exact resolve eq7445 eq7511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7445 eq7511
  have eq7634 : y = (M.op y y) := by
    first
    | (have i₁ := eq7585
       have i₂ := eq271 y
       grind)
    | exact superpose eq271 eq7585
    | exact resolve eq7585 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq7585
  have eq7664 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq662 X0 y y
       have i₂ := eq7634
       grind)
    | exact superpose eq7634 eq662
    | (have j0 := eq662 X0 x y
       grind)
    | exact resolve eq662 eq7634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662 eq7634
  have eq7667 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq7664 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7664
  have eq7718 : y = (M.op x y) := by
    first
    | (have i₁ := eq1338
       have i₂ := eq7667 x
       grind)
    | exact superpose eq7667 eq1338
    | exact resolve eq1338 eq7667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338 eq7667
  have eq7752 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq6716
       have i₂ := eq7718
       grind)
    | exact superpose eq7718 eq6716
    | exact resolve eq6716 eq7718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6716 eq7718
  have eq7776 : False := by grind
  exact eq7776

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_pxx_pxy_Equation422 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq345 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq346 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq347 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq345 X0 X1
       have j1 := eq346 X0 X1
       grind)
    | (have r₁ := eq345 X0 X1
       have r₂ := eq346 X0 X1
       grind)
    | exact resolve eq345 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq346
  have eq412 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq347 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq347
    | exact resolve eq347 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq445 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq412 X0 X2
       grind)
    | exact superpose eq412 eq9
    | (have j1 := eq412 X0 X2
       grind)
    | exact resolve eq9 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq577 : ∀ X0 X2 : G, (M.op X0 X0) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq9 X0 X0 x
       have i₂ := eq445 X0 x X2
       grind)
    | exact superpose eq445 eq9
    | (have j1 := eq445 X0 x X2
       grind)
    | exact resolve eq9 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq583 : ∀ X0 X2 : G, (M.op X2 X0) = (k X2 X0) := by
    intro X0 X2
    first
    | (have j0 := eq577 X0 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq577 x X2
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq577 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq630 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq583 (σ X1) (σ X0)
       grind)
    | exact superpose eq583 eq15
    | exact resolve eq15 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq657 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq630 X0 X1
       have i₂ := eq583 X1 X0
       grind)
    | exact superpose eq583 eq630
    | exact resolve eq630 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583 eq630
  have eq982 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq657 x y
       grind)
    | exact superpose eq657 eq16
    | (have r₁ := eq16
       have r₂ := eq657 x y
       grind)
    | exact resolve eq16 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq999 : False := by grind
  exact eq999

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation422 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq345 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq346 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq347 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq345 X0 X1
       have j1 := eq346 X0 X1
       grind)
    | (have r₁ := eq345 X0 X1
       have r₂ := eq346 X0 X1
       grind)
    | exact resolve eq345 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq346
  have eq410 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq347 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq347
    | exact resolve eq347 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq443 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq410 X0 X2
       grind)
    | exact superpose eq410 eq9
    | (have j1 := eq410 X0 X2
       grind)
    | exact resolve eq9 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq604 : ∀ X0 X2 : G, (M.op X0 X0) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq9 X0 X0 x
       have i₂ := eq443 X0 x X2
       grind)
    | exact superpose eq443 eq9
    | (have j1 := eq443 X0 x X2
       grind)
    | exact resolve eq9 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq612 : ∀ X0 X2 : G, (M.op X2 X0) = (k X2 X0) := by
    intro X0 X2
    first
    | (have j0 := eq604 X0 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq604 x X2
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq604 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq628 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq612 (σ X1) (σ X0)
       grind)
    | exact superpose eq612 eq15
    | exact resolve eq15 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq655 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq628 X0 X1
       have i₂ := eq612 X1 X0
       grind)
    | exact superpose eq612 eq628
    | exact resolve eq628 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612 eq628
  have eq977 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq655 x y
       grind)
    | exact superpose eq655 eq16
    | (have r₁ := eq16
       have r₂ := eq655 x y
       grind)
    | exact resolve eq16 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq993 : False := by grind
  exact eq993

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pxy_pyx_Equation422 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq345 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
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
  have eq346 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
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
  have eq347 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq345 X0 X1
       have j1 := eq346 X0 X1
       grind)
    | (have r₁ := eq345 X0 X1
       have r₂ := eq346 X0 X1
       grind)
    | exact resolve eq345 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq346
  have eq410 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq347 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq347
    | exact resolve eq347 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq443 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = X0 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq410 X0 X2
       grind)
    | exact superpose eq410 eq9
    | (have j1 := eq410 X0 X2
       grind)
    | exact resolve eq9 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq986 : ∀ X0 X2 : G, (M.op X0 X0) = X0 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq9 X0 X0 x
       have i₂ := eq443 X0 x X2
       grind)
    | exact superpose eq443 eq9
    | (have j1 := eq443 X0 x X2
       grind)
    | exact resolve eq9 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq1001 : ∀ X0 X2 : G, (k X2 X0) = (M.op X0 X2) := by
    intro X0 X2
    first
    | (have j0 := eq986 X0 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq986 x X2
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq986 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq1031 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1001 (σ X0) (σ X1)
       grind)
    | exact superpose eq1001 eq15
    | exact resolve eq15 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1062 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1031 X0 X1
       have i₂ := eq1001 X0 X1
       grind)
    | exact superpose eq1001 eq1031
    | exact resolve eq1031 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001 eq1031
  have eq1434 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1062 x y
       grind)
    | exact superpose eq1062 eq16
    | (have r₁ := eq16
       have r₂ := eq1062 x y
       grind)
    | exact resolve eq16 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1458 : False := by grind
  exact eq1458

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_pxy_pyy_pxy_Equation426 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
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
  have eq21 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq21 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq21 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq34 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq34 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq34 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq36 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 X0 X1
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq38
    | (have j0 := eq38 X0 X1
       grind)
    | exact resolve eq38 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq38
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq44 X0 X1
       grind)
    | (have r₁ := eq45 X0 X1
       have r₂ := eq44 X0 X1
       grind)
    | exact resolve eq45 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq45
  have eq89 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq93 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq89 X0 X1
       have j1 := eq47 X0 X1
       grind)
    | (have r₁ := eq89 X0 X1
       have r₂ := eq47 X0 X1
       grind)
    | (have r₁ := eq89 X0 X0
       have r₂ := eq47 X0 X0
       grind)
    | exact resolve eq89 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq89
  have eq191 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq93 (σ X0) (σ X1)
       grind)
    | exact superpose eq93 eq15
    | exact resolve eq15 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq191 X0 X1
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq191
    | exact resolve eq191 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq191
  have eq200 : False := by grind
  exact eq200

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation426 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X0 X0)))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  clear eq23
  have eq316 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
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
  clear eq316
  have eq322 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq318 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq334 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq322 (σ X0)
       grind)
    | exact superpose eq322 eq15
    | exact resolve eq15 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq340 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq322 (τ X0)
       grind)
    | exact superpose eq322 eq32
    | exact resolve eq32 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq340 X0
       have i₂ := eq322 X0
       grind)
    | exact superpose eq322 eq340
    | exact resolve eq340 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq353 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq334 X0
       have i₂ := eq322 X0
       grind)
    | exact superpose eq322 eq334
    | exact resolve eq334 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq688 : ∀ X0 X1 X2 : G, (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) ∨ (M.op (k (σ X1) X2) (σ X0)) = (M.op (σ X0) (k (σ X1) X2)) ∨ (k (σ X1) X2) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X1 X2 X0
       have i₂ := eq14 (k (σ X1) X2) (σ X0)
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 (σ X0) (k (σ X1) X2)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : ∀ X0 X1 X2 : G, (M.op (k (σ X1) X2) (σ X0)) = (M.op (σ X0) (k (σ X1) X2)) ∨ (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) ∨ (k (σ X1) X2) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq688 X0 X1 X2
       have i₂ := eq353 X0
       grind)
    | exact superpose eq353 eq688
    | (have j0 := eq688 X0 X1 X2
       grind)
    | exact resolve eq688 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq882811 : ∀ X0 X1 X2 : G, (M.op (σ X0) (k (σ X1) X2)) ≠ (M.op (σ X0) (k (σ X1) X2)) ∨ (k (σ X1) X2) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (k (σ X1) X2)) = (k (k (σ X1) X2) (σ X0)) ∨ (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) ∨ (k (σ X1) X2) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k (σ X1) X2) (σ X0)
       have i₂ := eq691 X0 X1 X2
       grind)
    | exact superpose eq691 eq13
    | (have j0 := eq13 (k (σ X1) X2) (σ X0)
       have j1 := eq691 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X0) (k (σ X1) X2)
       have r₂ := eq691 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k (σ X1) X2) (σ X0)
       have r₂ := eq691 X0 X1 X2
       grind)
    | exact resolve eq13 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq882917 : ∀ X0 X1 X2 : G, (k (σ X1) X2) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (k (σ X1) X2)) = (k (k (σ X1) X2) (σ X0)) ∨ (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) ∨ (k (σ X1) X2) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq882811 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882811
  have eq882996 : ∀ X0 X1 X2 : G, (k (σ X1) X2) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (k (σ X1) X2)) = (k (k (σ X1) X2) (σ X0)) ∨ (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) ∨ (k (σ X1) X2) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq882917 X0 X1 X2
       have i₂ := eq353 X0
       grind)
    | exact superpose eq353 eq882917
    | (have j0 := eq882917 X0 X1 X2
       grind)
    | exact resolve eq882917 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353 eq882917
  have eq882997 : ∀ X0 X1 X2 : G, (k (σ X1) X2) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (k (σ X1) X2)) = (k (k (σ X1) X2) (σ X0)) ∨ (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq882996 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882996
  have eq883240 : ∀ X0 X1 X2 : G, (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) ∨ (k (σ X1) X2) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq882997 X0 X1 X2
       have i₂ := eq28 X1 X2 X0
       grind)
    | exact superpose eq28 eq882997
    | (have j0 := eq882997 X0 X1 X2
       grind)
    | exact resolve eq882997 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq882997
  have eq883241 : ∀ X0 X1 X2 : G, (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) ∨ (k (σ X1) X2) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq883240 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883240
  have eq883929 : ∀ X0 X1 X2 : G, (σ (k (τ (k X0 X1)) X2)) = (M.op (σ X2) (k (σ (τ X0)) X1)) ∨ (k (σ (τ X0)) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq883241 X2 (τ X0) X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq883241
    | (have j0 := eq883241 X2 (τ X0) X1
       grind)
    | exact resolve eq883241 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883241
  have eq885250 : ∀ X0 X1 X2 : G, (σ (k (τ (k X0 X1)) X2)) = (M.op (σ X2) (k X0 X1)) ∨ (k (σ (τ X0)) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq883929 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq883929
    | (have j0 := eq883929 X0 X1 X2
       grind)
    | exact resolve eq883929 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883929
  have eq885505 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (M.op (σ X2) (k X0 X1)) ∨ (k (σ (τ X0)) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq885250 X0 X1 X2
       have i₂ := eq18 (k X0 X1) X2
       grind)
    | exact superpose eq18 eq885250
    | (have j0 := eq885250 X0 X1 X2
       grind)
    | exact resolve eq885250 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq885250
  have eq885684 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (M.op (σ X2) (k X0 X1)) ∨ (k X0 X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq885505 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq885505
    | (have j0 := eq885505 X0 X1 X2
       grind)
    | exact resolve eq885505 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885505
  have eq886455 : ∀ X0 X1 X2 : G, (k (k X1 X2) X0) = (M.op X0 (k X1 X2)) ∨ (σ (M.op (τ X0) (τ X0))) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq885684 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq885684
    | (have j0 := eq885684 X1 X2 (τ X0)
       grind)
    | exact resolve eq885684 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885684
  have eq887163 : ∀ X0 X1 X2 : G, (k X1 X2) = (σ (τ (M.op X0 X0))) ∨ (k (k X1 X2) X0) = (M.op X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq886455 X0 X1 X2
       have i₂ := eq347 X0
       grind)
    | exact superpose eq347 eq886455
    | (have j0 := eq886455 X0 X1 X2
       grind)
    | exact resolve eq886455 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347 eq886455
  have eq887260 : ∀ X0 X1 X2 : G, (k (k X1 X2) X0) = (M.op X0 (k X1 X2)) ∨ (M.op X0 X0) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq887163 X0 X1 X2
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq887163
    | (have j0 := eq887163 X0 X1 X2
       grind)
    | exact resolve eq887163 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887163
  have eq887348 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq887260 X0 X0 X0
       have i₂ := eq322 X0
       grind)
    | exact superpose eq322 eq887260
    | exact resolve eq887260 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq887507 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op X2 X2) ∨ (k (σ (k X0 X1)) X2) = (M.op X2 (σ (k X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq887260 X0 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq887260
    | exact resolve eq887260 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887260
  have eq889955 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    grind
  clear eq887348
  have eq890279 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq889955 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889955
  have eq1013150 : ∀ X0 X1 X2 : G, (k (σ (k X0 X1)) X2) = (M.op X2 (σ (k X0 X1))) ∨ (k (σ (k X0 X1)) X2) = (M.op X2 (σ (k X0 X1))) := by
    intro X0 X1 X2
    grind
  clear eq887507
  have eq1013557 : ∀ X0 X1 X2 : G, (k (σ (k X0 X1)) X2) = (M.op X2 (σ (k X0 X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1013150 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013150
  have eq1014148 : ∀ X0 X1 X2 : G, (k (σ (τ (k X0 X1))) X2) = (M.op X2 (σ (τ (k X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1013557 (τ X1) (τ X0) X2
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq1013557
    | exact resolve eq1013557 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1013557
  have eq1016150 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (M.op X2 (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1014148 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1014148
    | exact resolve eq1014148 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014148
  have eq1016921 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X1 X1)) X2) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1016150 (M.op X0 X0) X1 X2
       have i₂ := eq890279 X0 X1
       grind)
    | exact superpose eq890279 eq1016150
    | exact resolve eq1016150 eq890279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890279 eq1016150
  have eq1060306 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1016921 X0 (M.op X0 (M.op X0 X0)) x
       have i₂ := eq9 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq9 eq1016921
    | exact resolve eq1016921 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016921
  have eq1064445 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1060306 (σ X1) (σ X0)
       grind)
    | exact superpose eq1060306 eq15
    | exact resolve eq15 eq1060306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1065284 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1064445 X0 X1
       have i₂ := eq1060306 X1 X0
       grind)
    | exact superpose eq1060306 eq1064445
    | exact resolve eq1064445 eq1060306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060306 eq1064445
  have eq1085381 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1065284 x y
       grind)
    | exact superpose eq1065284 eq16
    | (have r₁ := eq16
       have r₂ := eq1065284 x y
       grind)
    | exact resolve eq16 eq1065284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065284
  have eq1085709 : False := by grind
  exact eq1085709

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_x_pxy_Equation426 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq37 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq82 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op (τ X1) (τ X1)) = X0 := by
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
  have eq84 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq143 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq438 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq82
    | exact resolve eq82 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq472 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq438 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq438
    | (have j0 := eq438 X0 X1
       grind)
    | exact resolve eq438 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq697 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq143 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq143
    | (have j0 := eq143 (σ X0) (σ X1)
       grind)
    | exact resolve eq143 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq3609 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq84 (σ X1) X1
       grind)
    | (have r₁ := eq13 (M.op (σ X1) (σ X1)) X1
       have r₂ := eq84 (M.op (M.op (σ X1) (σ X1)) X1) X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3619 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq84 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq3620 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3619 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3619
  have eq3622 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3609 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3609
  have eq3623 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3622 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3622
  have eq3625 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3620 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3620
    | (have j0 := eq3620 X0
       grind)
    | exact resolve eq3620 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3620
  have eq3667 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq3625 X0
       grind)
    | exact superpose eq3625 eq37
    | (have j1 := eq3625 X0
       grind)
    | exact resolve eq37 eq3625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq3625
  have eq3679 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3667 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3667
    | (have j0 := eq3667 X0
       grind)
    | exact resolve eq3667 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3667
  have eq3680 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3679 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3679
  have eq3683 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3680 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3680
    | exact resolve eq3680 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3707 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq3680 X0
       grind)
    | exact superpose eq3680 eq11
    | exact resolve eq11 eq3680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3680
  have eq3756 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3683 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq3683
    | exact resolve eq3683 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3683
  have eq3916 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3756 X0
       grind)
    | exact superpose eq3756 eq11
    | exact resolve eq11 eq3756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3756
  have eq3999 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3916 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3916
    | exact resolve eq3916 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3916
  have eq4627 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq4640 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq4627 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq4627
    | exact resolve eq4627 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4627
  have eq4676 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4640 X0
       have i₂ := eq3999 X0
       grind)
    | exact superpose eq3999 eq4640
    | exact resolve eq4640 eq3999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4640
  have eq4693 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq4676
  have eq29290 : ∀ X0 X1 : G, (σ (σ (τ X0))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq697 (τ X0) (τ X1)
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq697
    | (have j0 := eq697 (τ X0) (τ X1)
       grind)
    | exact resolve eq697 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq697
  have eq29392 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X0))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq29290 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq29290
    | (have j0 := eq29290 X0 X1
       grind)
    | exact resolve eq29290 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29290
  have eq29464 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq29392 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29392
    | (have j0 := eq29392 X0 X1
       grind)
    | exact resolve eq29392 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29392
  have eq29535 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq29464 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq29464
    | (have j0 := eq29464 X0 X1
       grind)
    | exact resolve eq29464 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29464
  have eq29600 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq29535 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29535
    | (have j0 := eq29535 X0 X1
       grind)
    | exact resolve eq29535 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29535
  have eq29654 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) (σ (τ X1)))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29600 X0 X1
       have i₂ := eq3707 (σ (τ X1))
       grind)
    | exact superpose eq3707 eq29600
    | (have j0 := eq29600 X0 X1
       grind)
    | exact resolve eq29600 eq3707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29600
  have eq29705 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (k (τ X1) (τ X1)))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29654 X0 X1
       have i₂ := eq15 (τ X1) (τ X1)
       grind)
    | exact superpose eq15 eq29654
    | (have j0 := eq29654 X0 X1
       grind)
    | exact resolve eq29654 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29654
  have eq29752 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29705 X0 X1
       have i₂ := eq19 X1 (τ X1)
       grind)
    | exact superpose eq19 eq29705
    | (have j0 := eq29705 X0 X1
       grind)
    | exact resolve eq29705 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq29705
  have eq29792 : ∀ X0 X1 : G, (σ (k X1 X1)) = (σ (σ (τ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29752 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq29752
    | (have j0 := eq29752 X0 X1
       grind)
    | exact resolve eq29752 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29752
  have eq29824 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29792 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29792
    | (have j0 := eq29792 X0 X1
       grind)
    | exact resolve eq29792 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29792
  have eq29851 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29824 X0 X1
       have i₂ := eq3999 X1
       grind)
    | exact superpose eq3999 eq29824
    | (have j0 := eq29824 X0 X1
       grind)
    | exact resolve eq29824 eq3999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29824
  have eq46541 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (σ X1)
       have i₂ := eq3623 (σ X0) X1
       grind)
    | exact superpose eq3623 eq29
    | (have j1 := eq3623 (σ X0) X1
       grind)
    | exact resolve eq29 eq3623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3623
  have eq46649 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq46541 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq46541
    | (have j0 := eq46541 X0 X1
       grind)
    | exact resolve eq46541 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46541
  have eq46746 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq46649 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46649
    | (have j0 := eq46649 X0 X1
       grind)
    | exact resolve eq46649 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46649
  have eq46839 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq46746 X0 X1
       have i₂ := eq3707 X1
       grind)
    | exact superpose eq3707 eq46746
    | (have j0 := eq46746 X0 X1
       grind)
    | exact resolve eq46746 eq3707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3707 eq46746
  have eq46915 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq46839 X0 X1
       have i₂ := eq3999 X1
       grind)
    | exact superpose eq3999 eq46839
    | (have j0 := eq46839 X0 X1
       grind)
    | exact resolve eq46839 eq3999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3999 eq46839
  have eq46966 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq46915 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46915
    | (have j0 := eq46915 X0 X1
       grind)
    | exact resolve eq46915 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46915
  have eq49104 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq46966 X0 X1
       grind)
    | exact superpose eq46966 eq11
    | (have j1 := eq46966 X0 X1
       grind)
    | exact resolve eq11 eq46966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46966
  have eq50358 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq49104 x y
       grind)
    | exact superpose eq49104 eq16
    | (have j1 := eq49104 x y
       grind)
    | exact resolve eq16 eq49104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49104
  have eq50852 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq50358
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq50358
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq50358 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50853 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (k x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq50358
       have i₂ := eq472 y x
       grind)
    | exact superpose eq472 eq50358
    | (have j1 := eq472 y x
       grind)
    | (have r₁ := eq50358
       have r₂ := eq472 y x
       grind)
    | exact resolve eq50358 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472 eq50358
  have eq50854 : (σ x) = (σ (M.op y y)) ∨ x = (k x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq50853
  have eq50855 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq50852
  have eq50856 : x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq50855
  have eq50858 : x = (k x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq50854
       have r₂ := eq13 x y
       grind)
    | exact resolve eq50854 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50854
  have eq51553 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq29851 x y
       have i₂ := eq50858
       grind)
    | exact superpose eq50858 eq29851
    | (have j0 := eq29851 x y
       grind)
    | exact resolve eq29851 eq50858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29851 eq50858
  have eq51558 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq51553
  have eq51559 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq51558
  have eq52256 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq51559
       grind)
    | exact superpose eq51559 eq16
    | exact resolve eq16 eq51559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51559
  have eq52269 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq52256
       have i₂ := eq50856
       grind)
    | exact superpose eq50856 eq52256
    | exact resolve eq52256 eq50856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50856 eq52256
  have eq52270 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq52269
  have eq52271 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq52270
  have eq52969 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4693 y
       have i₂ := eq52271
       grind)
    | exact superpose eq52271 eq4693
    | exact resolve eq4693 eq52271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52271
  have eq52992 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq52969
       have r₂ := eq16
       grind)
    | exact resolve eq52969 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52969
  have eq53019 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq52992
       grind)
    | exact superpose eq52992 eq10
    | exact resolve eq10 eq52992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52992
  have eq53162 : x = (M.op y y) := by
    first
    | (have i₁ := eq53019
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq53019
    | exact resolve eq53019 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53019
  have eq53376 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4693 y
       have i₂ := eq53162
       grind)
    | exact superpose eq53162 eq4693
    | exact resolve eq4693 eq53162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4693 eq53162
  have eq53402 : False := by grind
  exact eq53402

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_Equation426 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq37 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq85 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq142 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq542 : ∀ X0 X1 : G, (σ (σ X1)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq142 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq142
    | (have j0 := eq142 (σ X0) (σ X1)
       grind)
    | exact resolve eq142 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq2820 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq85 X1 X0
       grind)
    | exact superpose eq85 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq85 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq85 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq85 X0 (σ X0)
       grind)
    | exact resolve eq13 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2831 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq85 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq2832 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2831 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2831
  have eq2833 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2820 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2820
  have eq2834 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2833 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2833
  have eq2836 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2832 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2832
    | (have j0 := eq2832 X0
       grind)
    | exact resolve eq2832 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2832
  have eq2886 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq2836 X0
       grind)
    | exact superpose eq2836 eq37
    | (have j1 := eq2836 X0
       grind)
    | exact resolve eq37 eq2836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2836
  have eq2892 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2886 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2886
    | (have j0 := eq2886 X0
       grind)
    | exact resolve eq2886 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2886
  have eq2893 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2892 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2892
  have eq2895 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2893 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2893
    | exact resolve eq2893 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2918 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq2893 X0
       grind)
    | exact superpose eq2893 eq11
    | exact resolve eq11 eq2893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2893
  have eq2961 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2895 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq2895
    | exact resolve eq2895 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2895
  have eq3162 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq2961 X0
       grind)
    | exact superpose eq2961 eq11
    | exact resolve eq11 eq2961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3237 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3162 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3162
    | exact resolve eq3162 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3162
  have eq3295 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq3237 (τ X0)
       grind)
    | exact superpose eq3237 eq33
    | exact resolve eq33 eq3237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3342 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3295 X0
       have i₂ := eq2961 X0
       grind)
    | exact superpose eq2961 eq3295
    | exact resolve eq3295 eq2961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2961 eq3295
  have eq3821 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq3826 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq3821 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq3821
    | exact resolve eq3821 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3821
  have eq3853 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3826 X0
       have i₂ := eq3237 X0
       grind)
    | exact superpose eq3237 eq3826
    | exact resolve eq3826 eq3237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3826
  have eq3865 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq3853
  have eq21406 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X1) X0
       have i₂ := eq2834 (σ X0) X1
       grind)
    | exact superpose eq2834 eq23
    | (have j1 := eq2834 (σ X0) X1
       grind)
    | exact resolve eq23 eq2834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2834
  have eq21489 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21406 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq21406
    | (have j0 := eq21406 X0 X1
       grind)
    | exact resolve eq21406 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21406
  have eq21567 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21489 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21489
    | (have j0 := eq21489 X0 X1
       grind)
    | exact resolve eq21489 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21489
  have eq21636 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21567 X0 X1
       have i₂ := eq2918 X0
       grind)
    | exact superpose eq2918 eq21567
    | (have j0 := eq21567 X0 X1
       grind)
    | exact resolve eq21567 eq2918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21567
  have eq21682 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21636 X0 X1
       have i₂ := eq3237 X0
       grind)
    | exact superpose eq3237 eq21636
    | (have j0 := eq21636 X0 X1
       grind)
    | exact resolve eq21636 eq3237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21636
  have eq21719 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21682 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21682
    | (have j0 := eq21682 X0 X1
       grind)
    | exact resolve eq21682 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21682
  have eq24524 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (σ (M.op X1 X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq21719 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21719
    | (have j0 := eq21719 X1 (τ X0)
       grind)
    | exact resolve eq21719 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24605 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq21719 X1 X0
       grind)
    | exact superpose eq21719 eq11
    | (have j1 := eq21719 X1 X0
       grind)
    | exact resolve eq11 eq21719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21719
  have eq25205 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (σ (M.op (τ X1) (τ X1))) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq24524 X1 (τ X0)
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq24524
    | (have j0 := eq24524 X0 (τ X1)
       grind)
    | exact resolve eq24524 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24524
  have eq25391 : ∀ X0 X1 : G, (σ (τ (M.op X1 X1))) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25205 X0 X1
       have i₂ := eq3342 X1
       grind)
    | exact superpose eq3342 eq25205
    | (have j0 := eq25205 X0 X1
       grind)
    | exact resolve eq25205 eq3342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3342 eq25205
  have eq25473 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25391 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq25391
    | (have j0 := eq25391 X0 X1
       grind)
    | exact resolve eq25391 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25391
  have eq25547 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25473 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq25473
    | (have j0 := eq25473 X0 X1
       grind)
    | exact resolve eq25473 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25473
  have eq25960 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq25547 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25547
  have eq26275 : ∀ X0 X1 : G, (σ (σ (τ X1))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq542 (τ X0) (τ X1)
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq542
    | (have j0 := eq542 (τ X0) (τ X1)
       grind)
    | exact resolve eq542 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq542
  have eq26353 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X1))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq26275 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq26275
    | (have j0 := eq26275 X0 X1
       grind)
    | exact resolve eq26275 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26275
  have eq26407 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq26353 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq26353
    | (have j0 := eq26353 X0 X1
       grind)
    | exact resolve eq26353 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26353
  have eq26458 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (σ (τ X0))) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq26407 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26407
    | (have j0 := eq26407 X0 X1
       grind)
    | exact resolve eq26407 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26407
  have eq26506 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq26458 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26458
    | (have j0 := eq26458 X0 X1
       grind)
    | exact resolve eq26458 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26458
  have eq26546 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) (σ (τ X1)))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26506 X0 X1
       have i₂ := eq2918 (σ (τ X1))
       grind)
    | exact superpose eq2918 eq26506
    | (have j0 := eq26506 X0 X1
       grind)
    | exact resolve eq26506 eq2918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2918 eq26506
  have eq26584 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (k (τ X1) (τ X1)))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26546 X0 X1
       have i₂ := eq15 (τ X1) (τ X1)
       grind)
    | exact superpose eq15 eq26546
    | (have j0 := eq26546 X0 X1
       grind)
    | exact resolve eq26546 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26546
  have eq26620 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26584 X0 X1
       have i₂ := eq19 X1 (τ X1)
       grind)
    | exact superpose eq19 eq26584
    | (have j0 := eq26584 X0 X1
       grind)
    | exact resolve eq26584 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq26584
  have eq26649 : ∀ X0 X1 : G, (σ (k X1 X1)) = (σ (σ (τ X0))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26620 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq26620
    | (have j0 := eq26620 X0 X1
       grind)
    | exact resolve eq26620 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26620
  have eq26674 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26649 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26649
    | (have j0 := eq26649 X0 X1
       grind)
    | exact resolve eq26649 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26649
  have eq26699 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26674 X0 X1
       have i₂ := eq3237 X1
       grind)
    | exact superpose eq3237 eq26674
    | (have j0 := eq26674 X0 X1
       grind)
    | exact resolve eq26674 eq3237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3237 eq26674
  have eq29189 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24605 x y
       grind)
    | exact superpose eq24605 eq16
    | (have j1 := eq24605 x y
       grind)
    | exact resolve eq16 eq24605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24605
  have eq29981 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq29189
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq29189
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq29189 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29189
  have eq29984 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq29981
  have eq29985 : y = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq29984
  have eq29988 : (τ y) ≠ (τ y) ∨ x = (M.op y y) ∨ (τ y) = (τ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq25960 x y
       have i₂ := eq29985
       grind)
    | exact superpose eq29985 eq25960
    | (have j0 := eq25960 x y
       grind)
    | exact resolve eq25960 eq29985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25960
  have eq29992 : (τ y) ≠ (τ y) ∨ x = (M.op y y) ∨ (τ y) = (τ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq29988
  have eq29993 : x = (M.op y y) ∨ (τ y) = (τ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq29992
  have eq30432 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ y) = (τ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3865 y
       have i₂ := eq29993
       grind)
    | exact superpose eq29993 eq3865
    | exact resolve eq3865 eq29993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29993
  have eq30444 : (σ x) = (σ (M.op y y)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have r₁ := eq30432
       have r₂ := eq16
       grind)
    | exact resolve eq30432 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30432
  have eq30864 : (M.op y y) = (τ (σ x)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq30444
       grind)
    | exact superpose eq30444 eq10
    | exact resolve eq10 eq30444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30444
  have eq30984 : x = (M.op y y) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq30864
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30864
    | exact resolve eq30864 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30864
  have eq31054 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq3865 y
       have i₂ := eq30984
       grind)
    | exact superpose eq30984 eq3865
    | exact resolve eq3865 eq30984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30984
  have eq31066 : (τ y) = (τ (k x y)) := by
    first
    | (have r₁ := eq31054
       have r₂ := eq16
       grind)
    | exact resolve eq31054 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31054
  have eq31482 : (k x y) = (σ (τ y)) := by
    first
    | (have i₁ := eq11 (k x y)
       have i₂ := eq31066
       grind)
    | exact superpose eq31066 eq11
    | exact resolve eq11 eq31066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31066
  have eq31656 : y = (k x y) := by
    first
    | (have i₁ := eq31482
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq31482
    | exact resolve eq31482 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31482
  have eq31731 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq26699 x y
       have i₂ := eq31656
       grind)
    | exact superpose eq31656 eq26699
    | (have j0 := eq26699 x y
       grind)
    | exact resolve eq26699 eq31656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26699 eq31656
  have eq31732 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq31731
  have eq34267 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31732
       grind)
    | exact superpose eq31732 eq16
    | exact resolve eq16 eq31732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31732
  have eq34600 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq34267
       have i₂ := eq29985
       grind)
    | exact superpose eq29985 eq34267
    | exact resolve eq34267 eq29985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29985 eq34267
  have eq34601 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq34600
  have eq34602 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq34601
  have eq34618 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3865 y
       have i₂ := eq34602
       grind)
    | exact superpose eq34602 eq3865
    | exact resolve eq3865 eq34602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34602
  have eq34633 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq34618
       have r₂ := eq16
       grind)
    | exact resolve eq34618 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34618
  have eq34968 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq34633
       grind)
    | exact superpose eq34633 eq10
    | exact resolve eq10 eq34633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34633
  have eq35091 : x = (M.op y y) := by
    first
    | (have i₁ := eq34968
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq34968
    | exact resolve eq34968 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34968
  have eq35182 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3865 y
       have i₂ := eq35091
       grind)
    | exact superpose eq35091 eq3865
    | exact resolve eq3865 eq35091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3865 eq35091
  have eq35197 : False := by grind
  exact eq35197
