import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2659`: `x = ((x ◇ y) ◇ (x ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation2659 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2659 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2659.models_iff G M).mp hM
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
  have eq273 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq273 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq276 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq274 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq274 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq274 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq287 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq276 (σ X0)
       grind)
    | exact superpose eq276 eq15
    | exact resolve eq15 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq287 X0
       have i₂ := eq276 X0
       grind)
    | exact superpose eq276 eq287
    | exact resolve eq287 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276 eq287
  have eq352 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq306 X0
       grind)
    | exact superpose eq306 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq306 X0
       grind)
    | exact superpose eq306 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq356 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq352 X0 X1
       have j1 := eq354 X0 X1
       grind)
    | (have r₁ := eq352 X0 X1
       have r₂ := eq354 X0 X1
       grind)
    | exact resolve eq352 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq354
  have eq488 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq356 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq356
    | exact resolve eq356 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq499 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq356 X1 (σ X0)
       grind)
    | exact superpose eq356 eq15
    | (have j1 := eq356 X1 (σ X0)
       grind)
    | exact resolve eq15 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq539 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq488 X1 (τ X0)
       grind)
    | exact superpose eq488 eq17
    | (have j1 := eq488 X1 (τ X0)
       grind)
    | exact resolve eq17 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq488
  have eq643 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq539 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq539
    | exact resolve eq539 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq655 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq539 X1 X0
       grind)
    | exact superpose eq539 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq539 X1 X0
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq539 X0 X1
       grind)
    | exact resolve eq13 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq669 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (k (τ X1) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq655 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq683 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq643 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq643
    | (have j0 := eq643 X0 X1
       grind)
    | exact resolve eq643 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq2491 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq499 x y
       grind)
    | exact superpose eq499 eq16
    | (have j1 := eq499 x y
       grind)
    | exact resolve eq16 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2541 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq499 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq24283 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (k (τ X0) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) X1)
       have i₂ := eq669 X1 X0
       grind)
    | exact superpose eq669 eq10
    | (have j1 := eq669 X1 X0
       grind)
    | exact resolve eq10 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq24357 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (k (τ X0) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24283 X0 X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq24283
    | (have j0 := eq24283 X0 X1
       grind)
    | exact resolve eq24283 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24283
  have eq24402 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq24357 X0 X1
       have j1 := eq12 (τ X0) X1
       grind)
    | (have r₁ := eq24357 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq24357 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24357
  have eq24480 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24402 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24402
    | exact resolve eq24402 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24402
  have eq24840 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq2491
       have i₂ := eq24480 x y
       grind)
    | exact superpose eq24480 eq2491
    | (have j1 := eq24480 x y
       grind)
    | exact resolve eq2491 eq24480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2491
  have eq24841 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq24480 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24480
  have eq24842 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq24840
  have eq25182 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2541 x y
       have i₂ := eq24842
       grind)
    | exact superpose eq24842 eq2541
    | (have j0 := eq2541 x y
       grind)
    | exact resolve eq2541 eq24842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2541 eq24842
  have eq25212 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq25182
  have eq25213 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq25212
  have eq25220 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25213
       grind)
    | exact superpose eq25213 eq16
    | exact resolve eq16 eq25213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25243 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq24841 (σ x) (σ y)
       have i₂ := eq25213
       grind)
    | exact superpose eq25213 eq24841
    | (have j0 := eq24841 (σ x) (σ y)
       grind)
    | (have r₁ := eq24841 (σ x) (σ y)
       have r₂ := eq25213
       grind)
    | exact resolve eq24841 eq25213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24841 eq25213
  have eq25244 : (σ y) = (k (σ x) (σ y)) := by grind
  clear eq25243
  have eq25246 : (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq25244
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq25244
    | exact resolve eq25244 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25244
  have eq25272 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq683 x y
       have i₂ := eq25246
       grind)
    | exact superpose eq25246 eq683
    | (have j0 := eq683 x y
       grind)
    | exact resolve eq683 eq25246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683 eq25246
  have eq25373 : y = (M.op x y) := by
    first
    | (have r₁ := eq25272
       have r₂ := eq25220
       grind)
    | exact resolve eq25272 eq25220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25272
  have eq25428 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq25220
       have i₂ := eq25373
       grind)
    | exact superpose eq25373 eq25220
    | exact resolve eq25220 eq25373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25220 eq25373
  have eq25450 : False := by grind
  exact eq25450

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(Y,Y) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxy_y_pyy_x_pyx_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq66 (σ X0)
       grind)
    | exact superpose eq66 eq10
    | exact resolve eq10 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq43
    | exact resolve eq43 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq49
    | exact resolve eq49 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq70
    | exact resolve eq70 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq72 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq69
    | exact resolve eq69 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq68
    | exact resolve eq68 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq100 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq100
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq109
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq109
    | exact resolve eq109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq236 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
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
  have eq240 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq16
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq524 : ∀ X0 : G, (k (τ X0) (k x x)) = (τ (k X0 (k (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq282 X0 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq282
    | exact resolve eq282 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq282
  have eq558 : ∀ X0 : G, (τ (k X0 (M.op (σ x) (σ x)))) = (k (τ X0) (k x x)) := by
    intro X0
    first
    | (have i₁ := eq524 X0
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq524
    | exact resolve eq524 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq561 : ∀ X0 : G, (k (τ X0) (M.op x x)) = (τ (k X0 (M.op (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq558 X0
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq558
    | exact resolve eq558 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq565 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) X2)) y) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq566 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) X2)) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq574 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) X3) := by
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
  have eq586 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
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
  have eq695 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) X5)) X3) := by
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
  have eq1110 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) y) := by
    intro X0
    first
    | (have i₁ := eq586 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq586
    | (have j0 := eq586 x y X0
       grind)
    | exact resolve eq586 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1111 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq586
    | (have j0 := eq586 (σ x) (σ y) X0
       grind)
    | exact resolve eq586 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1125 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq586 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq586
    | (have j0 := eq586 x X0 y
       grind)
    | exact resolve eq586 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1126 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq586
    | (have j0 := eq586 (σ x) X0 (σ y)
       grind)
    | exact resolve eq586 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1130 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq586 X0 X1 x
       grind)
    | exact superpose eq586 eq14
    | exact resolve eq14 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1203 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1130 X0 (M.op X0 X1)
       have i₂ := eq586 X0 X0 X1
       grind)
    | exact superpose eq586 eq1130
    | exact resolve eq1130 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1204 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1130 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq1130 X0 (M.op X0 X0)
       grind)
    | exact superpose eq1130 eq1130
    | exact resolve eq1130 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1208 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1 X1 X0
       have i₂ := eq1130 (M.op X0 X1) X0
       grind)
    | exact superpose eq1130 eq55
    | exact resolve eq55 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1213 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X1
       have i₂ := eq1130 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq1130 eq14
    | exact resolve eq14 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1230 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1208 X0 X1
       have i₂ := eq586 X0 X1 X1
       grind)
    | exact superpose eq586 eq1208
    | exact resolve eq1208 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq1237 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1204 (σ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq1204
    | exact resolve eq1204 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq1204
  have eq1319 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq1125 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1125
    | (have j0 := eq1125 y
       grind)
    | exact resolve eq1125 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1359 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1319
       have i₂ := eq1110 X0
       grind)
    | exact superpose eq1110 eq1319
    | exact resolve eq1319 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1513 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq26 eq1126
    | (have j0 := eq1126 (σ y)
       grind)
    | exact resolve eq1126 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1553 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1111 eq1513
    | exact resolve eq1513 eq1111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1828 : (M.op x x) = (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op x x)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1203 (M.op x x) y
       have i₂ := eq1319
       grind)
    | exact superpose eq1319 eq1203
    | exact resolve eq1203 eq1319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319
  have eq1832 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq236 eq1203
    | exact resolve eq1203 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1834 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1513 eq1203
    | exact resolve eq1203 eq1513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1838 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq245 eq1203
    | exact resolve eq1203 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1868 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq1838
       have i₂ := eq1130 sF4 (M.op sF4 sF4)
       grind)
    | exact superpose eq1130 eq1838
    | exact resolve eq1838 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1838
  have eq1872 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1834
       have i₂ := eq1130 sF2 (M.op sF2 sF2)
       grind)
    | exact superpose eq1130 eq1834
    | exact resolve eq1834 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1834
  have eq1874 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1832
       have i₂ := eq1130 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq1130 eq1832
    | exact resolve eq1832 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1832
  have eq1878 : (M.op x x) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1828
       have i₂ := eq1130 x (M.op x x)
       grind)
    | exact superpose eq1130 eq1828
    | exact resolve eq1828 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130 eq1828
  have eq1917 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1868 eq245
    | exact resolve eq245 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1925 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1868 eq586
    | exact resolve eq586 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1938 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq1925 x
       have i₂ := eq586 sF4 sF2 x
       grind)
    | exact superpose eq586 eq1925
    | exact resolve eq1925 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925
  have eq1943 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq1868 eq1938
    | exact resolve eq1938 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1938
  have eq2002 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq1874 eq236
    | exact resolve eq236 eq1874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2011 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1874 eq586
    | exact resolve eq586 eq1874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2025 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq2011 x
       have i₂ := eq586 sF0 x x
       grind)
    | exact superpose eq586 eq2011
    | exact resolve eq2011 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2011
  have eq2030 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq1874 eq2025
    | exact resolve eq2025 eq1874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2025
  have eq2207 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq1868 eq1872
    | exact resolve eq1872 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1872
  have eq2208 : (M.op x x) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq1874 eq1878
    | exact resolve eq1878 eq1874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878
  have eq2945 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1230 (M.op X0 X1) X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq1230
    | exact resolve eq1230 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2947 : x = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | exact superpose eq236 eq1230
    | exact resolve eq1230 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2949 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq245 eq1230
    | exact resolve eq1230 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq2953 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1230 (M.op (M.op X0 X0) X0) (M.op X0 X1)
       have i₂ := eq1203 X0 X1
       grind)
    | exact superpose eq1203 eq1230
    | exact resolve eq1230 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3033 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2953 X0 X1
       have i₂ := eq1213 X0 X0
       grind)
    | exact superpose eq1213 eq2953
    | exact resolve eq2953 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213 eq2953
  have eq3039 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3033 X0 X1
       have i₂ := eq586 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq586 eq3033
    | exact resolve eq3033 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3033
  have eq3040 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3039 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq3039
    | exact resolve eq3039 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3039
  have eq3508 : (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = (M.op (M.op (M.op x y) y) x) := by
    first
    | exact superpose eq2947 eq3040
    | exact resolve eq3040 eq2947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3040
  have eq3596 : (M.op (M.op (M.op x y) (M.op x y)) y) = (M.op (M.op (M.op x y) y) x) := by
    first
    | (have i₁ := eq3508
       have i₂ := eq586 sF0 y y
       grind)
    | exact superpose eq586 eq3508
    | exact resolve eq3508 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3508
  have eq3632 : x = (M.op (M.op (M.op x y) y) x) := by
    first
    | exact superpose eq236 eq3596
    | exact resolve eq3596 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq3596
  have eq4047 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) y) := by
    intro X1
    first
    | exact superpose eq1359 eq240
    | (have j0 := eq240 y X1
       grind)
    | exact resolve eq240 eq1359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq4048 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) y) := by
    intro X1
    first
    | exact superpose eq1874 eq4047
    | exact resolve eq4047 eq1874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4047
  have eq4171 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2945 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq2945 X0 X1
       grind)
    | exact superpose eq2945 eq2945
    | exact resolve eq2945 eq2945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4179 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq4048 eq2945
    | exact resolve eq2945 eq4048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4048
  have eq4188 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq2947 eq2945
    | exact resolve eq2945 eq2947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4199 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq2949 eq2945
    | exact resolve eq2945 eq2949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4259 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq4199
       have i₂ := eq1230 sF2 sF4
       grind)
    | exact superpose eq1230 eq4199
    | exact resolve eq4199 eq1230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4199
  have eq4268 : (M.op (M.op x y) y) = (M.op (M.op x x) (M.op x y)) := by
    first
    | (have i₁ := eq4188
       have i₂ := eq1230 x sF0
       grind)
    | exact superpose eq1230 eq4188
    | exact resolve eq4188 eq1230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4188
  have eq4276 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op x (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq2002 eq4179
    | exact resolve eq4179 eq2002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2002 eq4179
  have eq4280 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4171 X0 X1
       have i₂ := eq1230 X0 (M.op X0 X1)
       grind)
    | exact superpose eq1230 eq4171
    | exact resolve eq4171 eq1230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4171
  have eq4308 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq1126 eq4259
    | exact resolve eq4259 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126 eq4259
  have eq4313 : (M.op (M.op x y) y) = (M.op (M.op x x) x) := by
    first
    | exact superpose eq1125 eq4268
    | exact resolve eq4268 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125 eq4268
  have eq4317 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op (M.op x y) x) X0)) := by
    intro X0
    first
    | exact superpose eq2208 eq4276
    | exact resolve eq4276 eq2208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2208 eq4276
  have eq4319 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4280 X0 X1
       have i₂ := eq586 X0 X0 X1
       grind)
    | exact superpose eq586 eq4280
    | exact resolve eq4280 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4280
  have eq4656 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1553 eq249
    | (have j0 := eq249 (σ y) X1
       grind)
    | exact resolve eq249 eq1553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq4657 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1868 eq4656
    | exact resolve eq4656 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4656
  have eq4762 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq4657 eq2945
    | exact resolve eq2945 eq4657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4657
  have eq4768 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq1917 eq4762
    | exact resolve eq4762 eq1917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1917 eq4762
  have eq4777 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq2207 eq4768
    | exact resolve eq4768 eq2207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2207 eq4768
  have eq7153 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4319 X0 X2
       have i₂ := eq4319 X0 X1
       grind)
    | (have i₁ := eq4319 X1 X1
       have i₂ := eq4319 X1 X1
       grind)
    | exact superpose eq4319 eq4319
    | exact resolve eq4319 eq4319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7164 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq4319 x X0
       have i₂ := eq4313
       grind)
    | exact superpose eq4313 eq4319
    | exact resolve eq4319 eq4313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4313
  have eq7165 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq4308 eq4319
    | exact resolve eq4319 eq4308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4308
  have eq7218 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1203 X0 X2
       have i₂ := eq4319 X0 X1
       grind)
    | (have i₁ := eq1203 X1 X1
       have i₂ := eq4319 X1 X1
       grind)
    | exact superpose eq4319 eq1203
    | exact resolve eq1203 eq4319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9438 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1359 eq565
    | (have j0 := eq565 y X1 X2
       grind)
    | exact resolve eq565 eq1359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565 eq1359
  have eq9439 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) x) X1)) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1874 eq9438
    | exact resolve eq9438 eq1874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1874 eq9438
  have eq9440 : ∀ X2 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x x) X2)) y) := by
    intro X2
    first
    | exact superpose eq4317 eq9439
    | exact resolve eq9439 eq4317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4317 eq9439
  have eq9445 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x y) (M.op x X0))) y) := by
    intro X0
    first
    | (have i₁ := eq9440 y
       have i₂ := eq1110 X0
       grind)
    | exact superpose eq1110 eq9440
    | exact resolve eq9440 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110 eq9440
  have eq9483 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) y) := by
    first
    | (have i₁ := eq9445 x
       have i₂ := eq586 sF0 x (M.op x x)
       grind)
    | exact superpose eq586 eq9445
    | exact resolve eq9445 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9445
  have eq9499 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) y) := by
    first
    | (have i₁ := eq9483
       have i₂ := eq1230 sF0 x
       grind)
    | exact superpose eq1230 eq9483
    | exact resolve eq9483 eq1230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9483
  have eq9512 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) x) y) := by
    first
    | exact superpose eq2030 eq9499
    | exact resolve eq9499 eq2030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2030 eq9499
  have eq9564 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1553 eq566
    | (have j0 := eq566 (σ y) X1 X2
       grind)
    | exact resolve eq566 eq1553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566 eq1553
  have eq9565 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1868 eq9564
    | exact resolve eq9564 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9564
  have eq9566 : ∀ X2 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ x)) X2)) (σ y)) := by
    intro X2
    first
    | exact superpose eq4777 eq9565
    | exact resolve eq9565 eq4777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4777 eq9565
  have eq9637 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) (σ y)) := by
    intro X0
    first
    | exact superpose eq1111 eq9566
    | exact resolve eq9566 eq1111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111 eq9566
  have eq9675 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq9637 x
       have i₂ := eq586 sF4 sF2 (M.op sF2 x)
       grind)
    | exact superpose eq586 eq9637
    | exact resolve eq9637 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9637
  have eq9691 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq9675
       have i₂ := eq1230 sF4 sF2
       grind)
    | exact superpose eq1230 eq9675
    | exact resolve eq9675 eq1230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230 eq9675
  have eq9704 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1943 eq9691
    | exact resolve eq9691 eq1943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1943 eq9691
  have eq10671 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) X0) X0) y) := by
    intro X0
    first
    | (have i₁ := eq9512
       have i₂ := eq7153 sF0 x x
       grind)
    | (have i₁ := eq9512
       have i₂ := eq7153 sF0 x x
       grind)
    | exact superpose eq7153 eq9512
    | exact resolve eq9512 eq7153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9512
  have eq10690 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9704
       have i₂ := eq7153 sF4 sF2 x
       grind)
    | (have i₁ := eq9704
       have i₂ := eq7153 sF4 x sF2
       grind)
    | exact superpose eq7153 eq9704
    | exact resolve eq9704 eq7153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7153 eq9704
  have eq17056 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) X3) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq574 X0 X1 x X3 X4
       have i₂ := eq586 X0 X1 x
       grind)
    | exact superpose eq586 eq574
    | exact resolve eq574 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq17173 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) (M.op (M.op X0 X0) (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17056 X0 (M.op X0 X1) X2 X2
       have i₂ := eq55 X0 X0 X1 X2
       grind)
    | exact superpose eq55 eq17056
    | exact resolve eq17056 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq17056
  have eq17274 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17173 X0 X1 X2
       have i₂ := eq586 (M.op X0 X0) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq586 eq17173
    | exact resolve eq17173 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17173
  have eq17384 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17274 X0 X1 X2
       have i₂ := eq586 X0 X0 X0
       grind)
    | exact superpose eq586 eq17274
    | exact resolve eq17274 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17274
  have eq17455 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17384 X0 X1 X2
       have i₂ := eq7218 X0 X0 X1
       grind)
    | exact superpose eq7218 eq17384
    | exact resolve eq17384 eq7218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17384
  have eq17495 : ∀ X0 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X0) X0) X2) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq17455 X0 x X2
       have i₂ := eq586 X0 X0 x
       grind)
    | exact superpose eq586 eq17455
    | exact resolve eq17455 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17455
  have eq27170 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) X5)) X3) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq695 X0 X1 x X3 X4 X5
       have i₂ := eq586 X0 X1 x
       grind)
    | exact superpose eq586 eq695
    | exact resolve eq695 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq38770 : (τ (k (k (σ x) (σ x)) (M.op (σ x) (σ x)))) = (k (k x x) (M.op x x)) := by
    first
    | exact superpose eq49 eq561
    | exact resolve eq561 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq561
  have eq38822 : (k (M.op x x) (M.op x x)) = (τ (k (k (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq38770
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq38770
    | exact resolve eq38770 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38770
  have eq38838 : (τ (k (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) = (k (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq38822
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq38822
    | exact resolve eq38822 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38822
  have eq38849 : (M.op (M.op x x) (M.op x x)) = (τ (k (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq38838
       have i₂ := eq66 (M.op x x)
       grind)
    | exact superpose eq66 eq38838
    | exact resolve eq38838 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38838
  have eq38860 : (M.op (M.op x x) (M.op x x)) = (τ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq38849
       have i₂ := eq66 (M.op sF2 sF2)
       grind)
    | exact superpose eq66 eq38849
    | exact resolve eq38849 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq38849
  have eq38871 : (M.op (M.op x x) (M.op x x)) = (τ (M.op (M.op (σ x) (σ x)) (σ x))) := by
    first
    | (have i₁ := eq38860
       have i₂ := eq586 sF2 sF2 sF2
       grind)
    | exact superpose eq586 eq38860
    | exact resolve eq38860 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38860
  have eq38881 : (M.op (M.op x x) (M.op x x)) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq7165 eq38871
    | exact resolve eq38871 eq7165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38871
  have eq38891 : (M.op (M.op x x) x) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq38881
       have i₂ := eq586 x x x
       grind)
    | exact superpose eq586 eq38881
    | exact resolve eq38881 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586 eq38881
  have eq38895 : (M.op (M.op x y) y) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq38891
       have i₂ := eq7164 x
       grind)
    | exact superpose eq7164 eq38891
    | exact resolve eq38891 eq7164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38891
  have eq43214 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) X2)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) (M.op X0 (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) X2))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27170 X0 X0 X1 X2 X0
       have i₂ := eq17495 X0 (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) X2)
       grind)
    | exact superpose eq17495 eq27170
    | exact resolve eq27170 eq17495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27170
  have eq43256 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) = (M.op (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X0 X1) X2))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43214 X0 X2 X2
       have i₂ := eq17495 X0 X2
       grind)
    | exact superpose eq17495 eq43214
    | exact resolve eq43214 eq17495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17495 eq43214
  have eq43339 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43256 X0 X1 X2
       have i₂ := eq14 X0 X1 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq14 eq43256
    | exact resolve eq43256 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43256
  have eq48843 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1237 (M.op (M.op x x) x)
       have i₂ := eq43339 x x x
       grind)
    | exact superpose eq43339 eq1237
    | exact resolve eq1237 eq43339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237 eq43339
  have eq49667 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X1) X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq48843 X0
       have i₂ := eq4319 X0 X1
       grind)
    | (have i₁ := eq48843 X1
       have i₂ := eq4319 X1 X1
       grind)
    | exact superpose eq4319 eq48843
    | exact resolve eq48843 eq4319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4319 eq48843
  have eq57394 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq57403 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq57394
    | exact resolve eq57394 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57394
  have eq57414 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq57403
       have r₂ := eq27
       grind)
    | exact resolve eq57403 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57403
  have eq57418 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq57414
    | exact resolve eq57414 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57414
  have eq57485 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq57418 eq1203
    | exact resolve eq1203 eq57418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203 eq57418
  have eq57504 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2949 eq57485
    | exact resolve eq57485 eq2949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2949 eq57485
  have eq57542 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq57504 eq2945
    | exact resolve eq2945 eq57504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57504
  have eq57561 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq7165 eq57542
    | exact resolve eq57542 eq7165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7165 eq57542
  have eq57928 : (τ (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq57561 eq38895
    | exact resolve eq38895 eq57561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38895 eq57561
  have eq58009 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq57928
    | exact resolve eq57928 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57928
  have eq59121 : y = (M.op (M.op (M.op x y) y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2945 y y
       have i₂ := eq58009
       grind)
    | exact superpose eq58009 eq2945
    | exact resolve eq2945 eq58009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58009
  have eq59138 : y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq2947 eq59121
    | exact resolve eq59121 eq2947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2947 eq59121
  have eq59185 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq59138 eq3632
    | exact resolve eq3632 eq59138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3632 eq59138
  have eq59251 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq59185
  have eq59307 : y = (M.op (M.op x x) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2945 y x
       have i₂ := eq59251
       grind)
    | exact superpose eq59251 eq2945
    | exact resolve eq2945 eq59251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2945
  have eq59319 : (σ y) = (M.op (σ (M.op x x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq49667 y x
       have i₂ := eq59251
       grind)
    | exact superpose eq59251 eq49667
    | exact resolve eq49667 eq59251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49667 eq59251
  have eq59322 : (σ y) = (M.op (σ (M.op x x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq59319
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq59319
    | exact resolve eq59319 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59319
  have eq59326 : y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq59307
       have i₂ := eq7164 x
       grind)
    | exact superpose eq7164 eq59307
    | exact resolve eq59307 eq7164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7164 eq59307
  have eq59331 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq59322
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq59322
    | exact resolve eq59322 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59322
  have eq59334 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1513 eq59331
    | exact resolve eq59331 eq1513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513 eq59331
  have eq59336 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1868 eq59334
    | exact resolve eq59334 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1868 eq59334
  have eq59399 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) X0) X0) y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq59326 eq7218
    | exact resolve eq7218 eq59326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59326
  have eq59410 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10671 eq59399
    | exact resolve eq59399 eq10671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10671 eq59399
  have eq59631 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq59336 eq7218
    | exact resolve eq7218 eq59336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7218 eq59336
  have eq59640 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10690 eq59631
    | exact resolve eq59631 eq10690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10690 eq59631
  have eq59720 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq72
       have i₂ := eq59410
       grind)
    | exact superpose eq59410 eq72
    | exact resolve eq72 eq59410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq59410
  have eq59903 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq59720
    | exact resolve eq59720 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59720
  have eq61372 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq59903 eq59640
    | exact resolve eq59640 eq59903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59640 eq59903
  have eq61465 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq61372
  have eq61495 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq61465
       have r₂ := eq27
       grind)
    | exact resolve eq61465 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61465
  have eq61522 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq61495 eq29
    | exact resolve eq29 eq61495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq61495
  have eq61705 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq61522
    | exact resolve eq61522 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq61522
  have eq61706 : x = y := by grind
  clear eq61705
  have eq61736 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq61706
       grind)
    | exact superpose eq61706 eq18
    | exact resolve eq18 eq61706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq61737 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq61706
       grind)
    | exact superpose eq61706 eq24
    | exact resolve eq24 eq61706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq61706
  have eq61925 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq61737
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq61737
    | exact resolve eq61737 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq61737
  have eq61958 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq61925 eq26
    | exact resolve eq26 eq61925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq61925
  have eq62432 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq61958 eq71
    | exact resolve eq71 eq61958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq61958
  have eq62617 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq62432
       have i₂ := eq61736
       grind)
    | exact superpose eq61736 eq62432
    | exact resolve eq62432 eq61736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61736 eq62432
  have eq62652 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62617 eq15
    | exact resolve eq15 eq62617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62617
  have eq62747 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq62652
    | exact resolve eq62652 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq62652
  have eq62773 : False := by grind
  exact eq62773

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(Y,Y) else if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxx_pxy_pyy_x_pxy_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq31 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 x y X0
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1) := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3) := by
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
  have eq56 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 (σ x) X0 (σ y)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq78 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq52 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq81 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) x) X0) := by
    intro X0
    first
    | exact superpose eq78 eq9
    | exact resolve eq9 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq56
    | (have j0 := eq56 (σ y)
       grind)
    | exact resolve eq56 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq89 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq86 eq9
    | exact resolve eq9 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) := by
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
  have eq116 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq65 eq116
    | exact resolve eq116 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq120 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq108 (σ X0)
       grind)
    | exact superpose eq108 eq15
    | exact resolve eq15 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq120 X0
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq120
    | exact resolve eq120 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq659 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq680 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq65
       have i₂ := eq14 sF2 sF3
       grind)
    | exact superpose eq14 eq65
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq65 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq681 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq680
    | exact resolve eq680 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq685 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq681
    | exact resolve eq681 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq687 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq685
    | exact resolve eq685 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq1229 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1235 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4)) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1 X4
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1265 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4)) = (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3))) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1229 (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1 X4
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq1229
    | exact resolve eq1229 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1279 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq1229 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1229
    | (have j0 := eq1229 x X0 y
       grind)
    | exact resolve eq1229 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1281 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1229 (M.op X0 X1) X2 (M.op X0 x)
       have i₂ := eq1229 X0 X1 x
       grind)
    | exact superpose eq1229 eq1229
    | exact resolve eq1229 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1296 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq1229
    | (have j0 := eq1229 (σ x) X0 (σ y)
       grind)
    | exact resolve eq1229 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1304 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq1229 X0 X1 x
       grind)
    | exact superpose eq1229 eq9
    | exact resolve eq9 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1319 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq121 (M.op X0 X1)
       have i₂ := eq1229 X0 X1 X1
       grind)
    | exact superpose eq1229 eq121
    | exact resolve eq121 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1325 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X1
       have i₂ := eq1229 (M.op X0 X1) X1 X2
       grind)
    | exact superpose eq1229 eq9
    | exact resolve eq9 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1331 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op X0 X0) X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X3
       have i₂ := eq1229 X0 X1 X2
       grind)
    | exact superpose eq1229 eq9
    | exact resolve eq9 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1370 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4)) = (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1) (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1265 X0 X1 X2 X3 X4
       have i₂ := eq1281 X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X1
       grind)
    | exact superpose eq1281 eq1265
    | exact resolve eq1265 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265 eq1281
  have eq1406 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4)) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1370 X0 X1 X2 X3 X4
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq1370
    | exact resolve eq1370 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq1370
  have eq1433 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1235 X0 X1 X2 X3 x
       have i₂ := eq1406 X0 X1 X2 X3 x
       grind)
    | exact superpose eq1406 eq1235
    | exact resolve eq1235 eq1406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235 eq1406
  have eq1443 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1433 X0 X1 X2 X3
       have i₂ := eq1331 X0 X1 X2 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)
       grind)
    | exact superpose eq1331 eq1433
    | exact resolve eq1433 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331 eq1433
  have eq1482 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1304 X0 (M.op X0 X1)
       have i₂ := eq1229 X0 X0 X1
       grind)
    | exact superpose eq1229 eq1304
    | exact resolve eq1304 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1483 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1304 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq1304 X0 (M.op X0 X0)
       grind)
    | exact superpose eq1304 eq1304
    | exact resolve eq1304 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1491 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq81 x
       have i₂ := eq1304 sF0 x
       grind)
    | exact superpose eq1304 eq81
    | exact resolve eq81 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq1492 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq89 sF2
       have i₂ := eq1304 sF4 sF2
       grind)
    | exact superpose eq1304 eq89
    | exact resolve eq89 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq1500 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1492 eq86
    | exact resolve eq86 eq1492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1538 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq1491 eq78
    | exact resolve eq78 eq1491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq1634 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq1491 eq121
    | exact resolve eq121 eq1491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1491
  have eq1638 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq20 eq1634
    | exact resolve eq1634 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1634
  have eq1655 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) X0) := by
    intro X0
    first
    | exact superpose eq1492 eq1304
    | exact resolve eq1304 eq1492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492
  have eq1815 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1 X1 X0
       have i₂ := eq1304 (M.op X0 X1) X0
       grind)
    | exact superpose eq1304 eq55
    | exact resolve eq55 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2151 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op (M.op (M.op x X0) (M.op x y)) (M.op (M.op x x) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op x x) X0 X1
       have i₂ := eq1279 X0
       grind)
    | exact superpose eq1279 eq9
    | exact resolve eq9 eq1279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2160 : ∀ X0 X1 : G, (M.op (M.op (M.op x x) (M.op x x)) X0) = (M.op (M.op (M.op x X0) (M.op x y)) (M.op (M.op x x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1229 (M.op x x) X0 X1
       have i₂ := eq1279 X0
       grind)
    | exact superpose eq1279 eq1229
    | exact resolve eq1229 eq1279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2163 : ∀ X0 X1 : G, (M.op (M.op (M.op x x) x) X0) = (M.op (M.op (M.op x X0) (M.op x y)) (M.op (M.op x x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2160 X0 X1
       have i₂ := eq1229 x x x
       grind)
    | exact superpose eq1229 eq2160
    | exact resolve eq2160 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2160
  have eq2210 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ x)) X1)) X0) := by
    intro X0 X1
    first
    | exact superpose eq1296 eq9
    | exact resolve eq9 eq1296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2219 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) X0) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ x)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1296 eq1229
    | exact resolve eq1229 eq1296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1296
  have eq2222 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ x)) (σ x)) X0) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ x)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2219 X0 X1
       have i₂ := eq1229 sF2 sF2 sF2
       grind)
    | exact superpose eq1229 eq2219
    | exact resolve eq2219 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2219
  have eq2273 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op x x)) (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1482 (M.op x x) X0
       have i₂ := eq1279 X0
       grind)
    | exact superpose eq1279 eq1482
    | exact resolve eq1482 eq1279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1279 eq1482
  have eq2317 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2273 X0
       have i₂ := eq1304 x (M.op x x)
       grind)
    | exact superpose eq1304 eq2273
    | exact resolve eq2273 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2273
  have eq2411 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq659 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq659
    | (have j0 := eq659 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq659 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq3412 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1325 (M.op X0 (M.op X0 X1)) (M.op X0 X1) X2
       have i₂ := eq9 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq9 eq1325
    | exact resolve eq1325 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3514 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X2) X0) = (M.op (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1229 (M.op (M.op X0 X1) X1) X2 (M.op (M.op X0 X1) x)
       have i₂ := eq1325 X0 X1 x
       grind)
    | exact superpose eq1325 eq1229
    | exact resolve eq1229 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3522 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1304 (M.op (M.op X0 X2) X2) X1
       have i₂ := eq1325 X0 X2 X2
       grind)
    | exact superpose eq1325 eq1304
    | exact resolve eq1304 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3524 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1483 (M.op (M.op X0 x) x)
       have i₂ := eq1325 X0 x x
       grind)
    | exact superpose eq1325 eq1483
    | exact resolve eq1483 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1483
  have eq3527 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3514 X0 X1 X2
       have i₂ := eq1325 X0 X1 X1
       grind)
    | exact superpose eq1325 eq3514
    | exact resolve eq3514 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3514
  have eq3579 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3412 X0 X1 x
       have i₂ := eq1443 X0 (M.op X0 X1) X1 x
       grind)
    | exact superpose eq1443 eq3412
    | exact resolve eq3412 eq1443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1443 eq3412
  have eq3880 : x = (M.op (M.op (M.op x y) y) x) := by
    first
    | (have i₁ := eq3524 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3524
    | (have j0 := eq3524 x y
       grind)
    | exact resolve eq3524 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3888 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq3524
    | (have j0 := eq3524 (σ x) (σ y)
       grind)
    | exact resolve eq3524 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3980 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op (M.op (M.op x y) y) X0) x) X0) := by
    intro X0
    first
    | exact superpose eq3880 eq9
    | exact resolve eq9 eq3880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3982 : x ≠ (M.op x (M.op (M.op x y) y)) ∨ (k x (M.op (M.op x y) y)) = (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq3880 eq12
    | (have j0 := eq12 x (M.op (M.op x y) y)
       grind)
    | exact resolve eq12 eq3880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3988 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) y) X0) x) = (M.op (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) X0) := by
    intro X0
    first
    | exact superpose eq3880 eq1229
    | exact resolve eq1229 eq3880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3989 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x x) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq3880 eq1325
    | exact resolve eq1325 eq3880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3991 : (M.op (M.op (M.op x y) y) x) = (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq3880 eq3579
    | exact resolve eq3579 eq3880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3992 : (M.op (M.op (M.op x y) y) x) = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | (have i₁ := eq3991
       have i₂ := eq1815 sF0 y
       grind)
    | exact superpose eq1815 eq3991
    | exact resolve eq3991 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3991
  have eq3993 : (M.op (M.op x x) x) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq3989 x
       have i₂ := eq1229 x x x
       grind)
    | exact superpose eq1229 eq3989
    | exact resolve eq3989 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3989
  have eq3994 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) y) X0) x) = (M.op (M.op (M.op (M.op x y) y) (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq3988 X0
       have i₂ := eq1815 sF0 y
       grind)
    | exact superpose eq1815 eq3988
    | exact resolve eq3988 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3988
  have eq3997 : (k x (M.op (M.op x y) y)) = (M.op (M.op (M.op x y) y) (M.op x y)) ∨ x ≠ (M.op x (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq3982
       have i₂ := eq1815 sF0 y
       grind)
    | exact superpose eq1815 eq3982
    | exact resolve eq3982 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3982
  have eq3998 : x = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | exact superpose eq3880 eq3992
    | exact resolve eq3992 eq3880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3992
  have eq4004 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) (M.op x y)) (M.op (M.op x x) X1)) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2163 X0 X1
       have i₂ := eq3993
       grind)
    | exact superpose eq3993 eq2163
    | exact resolve eq2163 eq3993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2163 eq3993
  have eq4023 : x = (k x (M.op (M.op x y) y)) ∨ x ≠ (M.op x (M.op (M.op x y) y)) := by
    first
    | exact superpose eq3998 eq3997
    | exact resolve eq3997 eq3998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3997
  have eq4024 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) y) X0) x) := by
    intro X0
    first
    | exact superpose eq3998 eq3994
    | exact resolve eq3994 eq3998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3994 eq3998
  have eq4035 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) y) X0) X0) := by
    intro X0
    first
    | exact superpose eq4004 eq2151
    | exact resolve eq2151 eq4004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2151 eq4004
  have eq4049 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | exact superpose eq4024 eq3980
    | exact resolve eq3980 eq4024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3980 eq4024
  have eq4081 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq3888 eq9
    | exact resolve eq9 eq3888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4089 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq3888 eq1229
    | exact resolve eq1229 eq3888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4090 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq3888 eq1325
    | exact resolve eq1325 eq3888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325
  have eq4092 : (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq3888 eq3579
    | exact resolve eq3579 eq3888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4093 : (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq4092
       have i₂ := eq1815 sF4 sF3
       grind)
    | exact superpose eq1815 eq4092
    | exact resolve eq4092 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4092
  have eq4094 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq4090 x
       have i₂ := eq1229 sF2 sF2 x
       grind)
    | exact superpose eq1229 eq4090
    | exact resolve eq4090 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229 eq4090
  have eq4095 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | (have i₁ := eq4089 X0
       have i₂ := eq1815 sF4 sF3
       grind)
    | exact superpose eq1815 eq4089
    | exact resolve eq4089 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815 eq4089
  have eq4099 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3888 eq4093
    | exact resolve eq4093 eq3888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3888 eq4093
  have eq4105 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ x)) X1)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0 X1
    first
    | exact superpose eq4094 eq2222
    | exact resolve eq2222 eq4094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2222 eq4094
  have eq4125 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq4099 eq4095
    | exact resolve eq4095 eq4099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4095 eq4099
  have eq4136 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq4105 eq2210
    | exact resolve eq2210 eq4105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2210 eq4105
  have eq4150 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq4125 eq4081
    | exact resolve eq4081 eq4125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4081 eq4125
  have eq4695 : (M.op x x) = (M.op x (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq2317 sF0
       have i₂ := eq4049 sF0
       grind)
    | exact superpose eq4049 eq2317
    | exact resolve eq2317 eq4049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2317
  have eq4718 : x ≠ (M.op x x) ∨ x = (k x (M.op (M.op x y) y)) := by
    first
    | exact superpose eq4695 eq4023
    | exact resolve eq4023 eq4695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4023
  have eq4759 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq4150 eq9
    | exact resolve eq9 eq4150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4875 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op (M.op (M.op x y) y) x) ∨ x = (k x (M.op (M.op x y) y)) := by
    first
    | exact superpose eq4695 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x (M.op (M.op x y) y)
       have r₂ := eq4695
       grind)
    | exact resolve eq13 eq4695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4695
  have eq4887 : (M.op x x) = (M.op (M.op (M.op x y) y) x) ∨ x = (k x (M.op (M.op x y) y)) := by grind
  clear eq4875
  have eq4893 : x = (M.op x x) ∨ x = (k x (M.op (M.op x y) y)) := by
    first
    | exact superpose eq3880 eq4887
    | exact resolve eq4887 eq3880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3880 eq4887
  have eq4901 : x = (k x (M.op (M.op x y) y)) := by
    first
    | (have r₁ := eq4893
       have r₂ := eq4718
       grind)
    | exact resolve eq4893 eq4718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4718 eq4893
  have eq5196 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3522 (M.op (M.op X0 X1) (M.op X0 X2)) X3 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq3522
    | exact resolve eq3522 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5310 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X0 X1 X2 X0
       have i₂ := eq3522 (M.op (M.op X0 X1) (M.op X0 X2)) X0 X3
       grind)
    | (have i₁ := eq55 X0 X1 X2 X0
       have i₂ := eq3522 (M.op (M.op X0 X1) (M.op X0 X2)) X3 X0
       grind)
    | exact superpose eq3522 eq55
    | exact resolve eq55 eq3522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq5447 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5310 X0 X1 X2 x
       have i₂ := eq5196 X0 X1 X2 x
       grind)
    | exact superpose eq5196 eq5310
    | exact resolve eq5310 eq5196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5196 eq5310
  have eq6338 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) X0) X0) y) := by
    intro X0
    first
    | (have i₁ := eq4035 y
       have i₂ := eq3522 sF0 y x
       grind)
    | (have i₁ := eq4035 y
       have i₂ := eq3522 sF0 x y
       grind)
    | exact superpose eq3522 eq4035
    | exact resolve eq4035 eq3522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4035
  have eq6378 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4136 sF3
       have i₂ := eq3522 sF4 sF3 x
       grind)
    | (have i₁ := eq4136 sF3
       have i₂ := eq3522 sF4 x sF3
       grind)
    | exact superpose eq3522 eq4136
    | exact resolve eq4136 eq3522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4136
  have eq11513 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3527 X0 X1 X1
       have i₂ := eq3522 (M.op X0 X1) X1 X2
       grind)
    | (have i₁ := eq3527 X0 X1 X1
       have i₂ := eq3522 (M.op X0 X1) X2 X1
       grind)
    | exact superpose eq3522 eq3527
    | exact resolve eq3527 eq3522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3522 eq3527
  have eq101496 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq2411 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2411
    | (have j0 := eq2411 x y
       grind)
    | exact resolve eq2411 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2411
  have eq101623 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq101496
    | exact resolve eq101496 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101496
  have eq101741 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq101623
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq101623
    | exact resolve eq101623 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101623
  have eq101841 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq101741
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq101741
    | exact resolve eq101741 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101741
  have eq101923 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq101841
    | exact resolve eq101841 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101841
  have eq101981 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq101923
       have r₂ := eq27
       grind)
    | exact resolve eq101923 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101923
  have eq102026 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq101981
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq101981
    | exact resolve eq101981 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101981
  have eq102060 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq102026
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq102026
    | exact resolve eq102026 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102026
  have eq102085 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq102060
    | exact resolve eq102060 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102060
  have eq102108 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq102085
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq102085
    | exact resolve eq102085 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102085
  have eq102128 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq102108
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq102108
    | exact resolve eq102108 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102108
  have eq102136 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq102128
    | exact resolve eq102128 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102128
  have eq102197 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq102136 eq11513
    | exact resolve eq11513 eq102136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102136
  have eq102214 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq6378 eq102197
    | exact resolve eq102197 eq6378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102197
  have eq102215 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq102214
  have eq102229 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq102215 eq118
    | (have r₁ := eq118
       have r₂ := eq102215
       grind)
    | exact resolve eq118 eq102215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq102215
  have eq102347 : (σ x) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq102229
  have eq109488 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (σ (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq1319 x x
       have i₂ := eq4049 x
       grind)
    | exact superpose eq4049 eq1319
    | exact resolve eq1319 eq4049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319 eq4049
  have eq109765 : (σ (M.op (M.op x y) y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq109488
       have i₂ := eq121 x
       grind)
    | exact superpose eq121 eq109488
    | exact resolve eq109488 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109488
  have eq109899 : (σ (M.op (M.op x y) y)) = (M.op (M.op (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq109765
       have i₂ := eq5447 (σ x) (σ x) (σ x)
       grind)
    | exact superpose eq5447 eq109765
    | exact resolve eq109765 eq5447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5447 eq109765
  have eq110181 : (M.op (M.op (σ x) (σ x)) (σ x)) = (σ (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq109899
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq109899
    | exact resolve eq109899 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109899
  have eq110387 : (M.op (M.op (σ x) (σ y)) (σ y)) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq4150 eq110181
    | exact resolve eq110181 eq4150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4150 eq110181
  have eq130178 : (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq102347
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq102347
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq102347 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130190 : (τ (σ x)) = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq102347
       grind)
    | exact superpose eq102347 eq10
    | exact resolve eq10 eq102347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102347
  have eq130262 : x = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq38 eq130190
    | exact resolve eq130190 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130190
  have eq130272 : (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq130178
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq130178
    | exact resolve eq130178 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130178
  have eq130275 : x = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq130262
       have r₂ := eq115
       grind)
    | exact resolve eq130262 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq130262
  have eq130285 : (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq130272
    | exact resolve eq130272 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130272
  have eq130295 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq130285
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq130285
    | exact resolve eq130285 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130285
  have eq130296 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq130295
  have eq130304 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq130296
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq130296
    | exact resolve eq130296 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130296
  have eq130305 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq130304
  have eq132012 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq687
       have i₂ := eq130275
       grind)
    | exact superpose eq130275 eq687
    | exact resolve eq687 eq130275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687 eq130275
  have eq132027 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq132012
  have eq132041 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq132027
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq132027
    | exact resolve eq132027 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132027
  have eq132128 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq130305 eq3524
    | exact resolve eq3524 eq130305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130305
  have eq132188 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1500 eq132128
    | exact resolve eq132128 eq1500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1500 eq132128
  have eq132239 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) X0) X0) y) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq11513 y x x
       have i₂ := eq132188
       grind)
    | exact superpose eq132188 eq11513
    | exact resolve eq11513 eq132188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132188
  have eq132256 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6338 eq132239
    | exact resolve eq132239 eq6338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6338 eq132239
  have eq132257 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq132256
  have eq132306 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq121 x
       have i₂ := eq132257
       grind)
    | exact superpose eq132257 eq121
    | exact resolve eq121 eq132257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132257
  have eq132417 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq132306
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq132306
    | exact resolve eq132306 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132306
  have eq132443 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq132417
    | exact resolve eq132417 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq132417
  have eq132576 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq132443 eq4759
    | exact resolve eq4759 eq132443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4759
  have eq132621 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq132443 eq3579
    | exact resolve eq3579 eq132443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3579
  have eq333755 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq132041 eq11513
    | exact resolve eq11513 eq132041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11513 eq132041
  have eq333764 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq6378 eq333755
    | exact resolve eq333755 eq6378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6378 eq333755
  have eq333765 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq333764
  have eq333801 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq333765 eq132443
    | exact resolve eq132443 eq333765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132443
  have eq334061 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq333801
       have r₂ := eq27
       grind)
    | exact resolve eq333801 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333801
  have eq334150 : y = (M.op (M.op (M.op x y) x) y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3524 y x
       have i₂ := eq334061
       grind)
    | exact superpose eq334061 eq3524
    | exact resolve eq3524 eq334061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334061
  have eq334203 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1538 eq334150
    | exact resolve eq334150 eq1538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334150
  have eq334289 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq334203 eq132576
    | exact resolve eq132576 eq334203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132576
  have eq334490 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq334289
  have eq334529 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq334490
    | exact resolve eq334490 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq334490
  have eq335477 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq334203 eq334529
    | exact resolve eq334529 eq334203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334203 eq334529
  have eq335934 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq335477
  have eq339517 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq335934 eq132621
    | exact resolve eq132621 eq335934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132621 eq335934
  have eq339941 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq339517
  have eq340033 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq339941 eq39
    | exact resolve eq39 eq339941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq339941
  have eq340140 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq38 eq340033
    | exact resolve eq340033 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340033
  have eq340141 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq340140
  have eq340153 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq340141 eq38
    | exact resolve eq38 eq340141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq340343 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq37 eq340153
    | exact resolve eq340153 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq340153
  have eq340408 : x = (k x (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq340343 eq4901
    | exact resolve eq4901 eq340343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4901
  have eq340775 : x = (k x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq340408
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq340408
    | exact resolve eq340408 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq340408
  have eq341025 : x = (k x x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq340343 eq340775
    | exact resolve eq340775 eq340343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340343 eq340775
  have eq341031 : x = (k x x) ∨ x = y := by grind
  clear eq341025
  have eq341033 : x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq341031
       have i₂ := eq108 x
       grind)
    | exact superpose eq108 eq341031
    | exact resolve eq341031 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq341031
  have eq341644 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq121 x
       have i₂ := eq341033
       grind)
    | exact superpose eq341033 eq121
    | exact resolve eq121 eq341033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq341033
  have eq341802 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq341644
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq341644
    | exact resolve eq341644 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341644
  have eq342644 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq341802 eq333765
    | exact resolve eq333765 eq341802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333765 eq341802
  have eq342850 : (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq342644
  have eq369933 : y = (M.op (M.op (M.op x y) x) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq3524 y x
       have i₂ := eq342850
       grind)
    | exact superpose eq342850 eq3524
    | exact resolve eq3524 eq342850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3524 eq342850
  have eq369986 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1538 eq369933
    | exact resolve eq369933 eq1538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538 eq369933
  have eq369987 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq369986
  have eq369992 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq369987 eq27
    | exact resolve eq27 eq369987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369987
  have eq370810 : x = y := by
    first
    | (have r₁ := eq369992
       have r₂ := eq340141
       grind)
    | exact resolve eq369992 eq340141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340141 eq369992
  have eq370831 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq370810
       grind)
    | exact superpose eq370810 eq24
    | exact resolve eq24 eq370810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq373999 : (M.op (M.op (σ x) (σ y)) (σ y)) = (σ (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq110387
       have i₂ := eq370810
       grind)
    | exact superpose eq370810 eq110387
    | exact resolve eq110387 eq370810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110387 eq370810
  have eq389432 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq1638 eq373999
    | exact resolve eq373999 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638 eq373999
  have eq390617 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq370831
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq370831
    | exact resolve eq370831 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq370831
  have eq398613 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq390617 eq389432
    | exact resolve eq389432 eq390617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389432 eq390617
  have eq399073 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) X0) := by
    intro X0
    first
    | exact superpose eq398613 eq1655
    | exact resolve eq1655 eq398613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1655 eq398613
  have eq401288 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq399073 x
       have i₂ := eq1304 sF1 x
       grind)
    | exact superpose eq1304 eq399073
    | exact resolve eq399073 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304 eq399073
  have eq402488 : False := by grind
  exact eq402488

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyx_pyy_pxy_y_pyx_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq66 (σ X0)
       grind)
    | exact superpose eq66 eq10
    | exact resolve eq10 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq43
    | exact resolve eq43 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq70 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq49
    | exact resolve eq49 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq70
    | exact resolve eq70 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq72 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq69
    | exact resolve eq69 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq68
    | exact resolve eq68 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq77 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (M.op y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq100 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq100
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq16
    | exact resolve eq16 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq109
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq109
    | exact resolve eq109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y x) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq236 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
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
  clear eq50
  have eq243 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
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
  clear eq52
  have eq855 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq73 X1
       grind)
    | exact superpose eq73 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq856 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq855 X0 X1
       have i₂ := eq73 X1
       grind)
    | exact superpose eq73 eq855
    | (have j0 := eq855 X0 X1
       grind)
    | exact resolve eq855 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq855
  have eq895 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq856 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq856
    | (have j0 := eq856 y X0
       grind)
    | exact resolve eq856 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq1087 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x x) X0) := by
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
  have eq1088 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq655
    | (have j0 := eq655 (σ x) X0 (σ y)
       grind)
    | exact resolve eq655 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1092 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
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
  have eq1160 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1092 (M.op X0 X1) X2
       have i₂ := eq655 X0 X1 X1
       grind)
    | exact superpose eq655 eq1092
    | exact resolve eq1092 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1164 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1092 X0 (M.op X0 X1)
       have i₂ := eq655 X0 X0 X1
       grind)
    | exact superpose eq655 eq1092
    | exact resolve eq1092 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1169 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1 X1 X0
       have i₂ := eq1092 (M.op X0 X1) X0
       grind)
    | exact superpose eq1092 eq55
    | exact resolve eq55 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1174 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X1
       have i₂ := eq1092 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq1092 eq14
    | exact resolve eq14 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1189 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1169 X0 X1
       have i₂ := eq655 X0 X1 X1
       grind)
    | exact superpose eq655 eq1169
    | exact resolve eq1169 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq1271 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq1087 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1087
    | (have j0 := eq1087 y
       grind)
    | exact resolve eq1087 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq1353 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq26 eq1088
    | (have j0 := eq1088 (σ y)
       grind)
    | exact resolve eq1088 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq1562 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq236 eq1164
    | exact resolve eq1164 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1568 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq243 eq1164
    | exact resolve eq1164 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1599 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq1568
       have i₂ := eq1092 sF4 (M.op sF4 sF4)
       grind)
    | exact superpose eq1092 eq1568
    | exact resolve eq1568 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1568
  have eq1605 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1562
       have i₂ := eq1092 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq1092 eq1562
    | exact resolve eq1562 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092 eq1562
  have eq1648 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1599 eq243
    | exact resolve eq243 eq1599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq1732 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq1605 eq236
    | exact resolve eq236 eq1605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq2561 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1189 (M.op X0 X1) X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq1189
    | exact resolve eq1189 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2569 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1189 (M.op (M.op X0 X0) X0) (M.op X0 X1)
       have i₂ := eq1164 X0 X1
       grind)
    | exact superpose eq1164 eq1189
    | exact resolve eq1189 eq1164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164
  have eq2646 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2569 X0 X1
       have i₂ := eq1174 X0 X0
       grind)
    | exact superpose eq1174 eq2569
    | exact resolve eq2569 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174 eq2569
  have eq2653 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2646 X0 X1
       have i₂ := eq655 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq655 eq2646
    | exact resolve eq2646 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2646
  have eq2654 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2653 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq2653
    | exact resolve eq2653 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2653
  have eq2977 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq2654 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2654
    | (have j0 := eq2654 x y
       grind)
    | exact resolve eq2654 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2983 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq2654
    | (have j0 := eq2654 (σ x) (σ y)
       grind)
    | exact resolve eq2654 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3118 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op (M.op x y) x) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq2977 eq12
    | (have j0 := eq12 (M.op x y) x
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq2977
       grind)
    | exact resolve eq12 eq2977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2977
  have eq3131 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (k (M.op x y) x) := by grind
  clear eq3118
  have eq3139 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq2983 eq12
    | (have j0 := eq12 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq2983
       grind)
    | exact resolve eq12 eq2983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2983
  have eq3152 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq3139
  have eq3941 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2654 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq2561 X0 X1
       grind)
    | exact superpose eq2561 eq2654
    | exact resolve eq2654 eq2561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2561 eq2654
  have eq3942 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3941 X0 X1
       have i₂ := eq655 (M.op X0 X1) X1 X1
       grind)
    | exact superpose eq655 eq3941
    | exact resolve eq3941 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655 eq3941
  have eq3993 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3942 X0 X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq3942
    | exact resolve eq3942 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3942
  have eq8332 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq895 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq895
    | (have j0 := eq895 x
       grind)
    | exact resolve eq895 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq8363 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq8332
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq8332
    | exact resolve eq8332 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8332
  have eq8382 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq8363
    | exact resolve eq8363 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8363
  have eq8396 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq8382
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq8382
    | exact resolve eq8382 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8382
  have eq8408 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq8396
    | exact resolve eq8396 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8396
  have eq8418 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq8408
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq8408
    | exact resolve eq8408 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8408
  have eq43300 : x = (M.op (M.op x x) y) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq3131 eq1732
    | exact resolve eq1732 eq3131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1732 eq3131
  have eq43409 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq43300
       have i₂ := eq1271
       grind)
    | exact superpose eq1271 eq43300
    | exact resolve eq43300 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271 eq43300
  have eq43421 : x = (k (M.op x y) x) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1605 eq43409
    | exact resolve eq43409 eq1605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1605 eq43409
  have eq45363 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq3152 eq1648
    | exact resolve eq1648 eq3152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3152
  have eq45462 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1353 eq45363
    | exact resolve eq45363 eq1353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1353 eq45363
  have eq45475 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1599 eq45462
    | exact resolve eq45462 eq1599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1599 eq45462
  have eq51227 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1160 X0 X1 X2
       have i₂ := eq1189 X0 X1
       grind)
    | (have i₁ := eq1160 X1 X1 X2
       have i₂ := eq1189 X1 X1
       grind)
    | exact superpose eq1189 eq1160
    | exact resolve eq1160 eq1189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189
  have eq75457 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x x) y) X0) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq51227 y x x
       have i₂ := eq117
       grind)
    | exact superpose eq117 eq51227
    | exact resolve eq51227 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq75493 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (σ y)) X0) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq8418 eq51227
    | exact resolve eq51227 eq8418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8418 eq51227
  have eq75846 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq75493 x
       have i₂ := eq1160 sF2 sF3 x
       grind)
    | exact superpose eq1160 eq75493
    | exact resolve eq75493 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75493
  have eq75851 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq75457 x
       have i₂ := eq1160 x y x
       grind)
    | exact superpose eq1160 eq75457
    | exact resolve eq75457 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160 eq75457
  have eq76090 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq75846
    | exact resolve eq75846 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75846
  have eq76091 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq76090
  have eq76093 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq75851
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq75851
    | exact resolve eq75851 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75851
  have eq76094 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq76093
  have eq76206 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq76094 eq76091
    | exact resolve eq76091 eq76094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76217 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq76206
       have r₂ := eq27
       grind)
    | exact resolve eq76206 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76206
  have eq76243 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq76217 eq78
    | (have r₁ := eq78
       have r₂ := eq76217
       grind)
    | exact resolve eq78 eq76217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq76217
  have eq76386 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq76243
  have eq104854 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq76386 eq3993
    | exact resolve eq3993 eq76386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3993 eq76386
  have eq104872 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1648 eq104854
    | exact resolve eq104854 eq1648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648 eq104854
  have eq104883 : (τ (σ x)) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq104872 eq114
    | exact resolve eq114 eq104872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq104891 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq104872 eq76094
    | exact resolve eq76094 eq104872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76094 eq104872
  have eq104901 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq104891
  have eq104914 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq28 eq104883
    | exact resolve eq104883 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104883
  have eq104928 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq104901
       grind)
    | exact superpose eq104901 eq72
    | exact resolve eq72 eq104901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104901
  have eq105145 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq104928
    | exact resolve eq104928 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104928
  have eq106507 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq104914
       grind)
    | exact superpose eq104914 eq72
    | exact resolve eq72 eq104914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106508 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq77
       have i₂ := eq104914
       grind)
    | exact superpose eq104914 eq77
    | (have r₁ := eq77
       have r₂ := eq104914
       grind)
    | exact resolve eq77 eq104914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq106648 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq106508
  have eq106649 : (M.op x y) = (M.op y x) ∨ x = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq106648
  have eq106726 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq20 eq106507
    | exact resolve eq106507 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106507
  have eq109826 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq106649
       grind)
    | exact superpose eq106649 eq13
    | exact resolve eq13 eq106649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106649
  have eq109864 : (M.op x y) = (k y x) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq109826
       have r₂ := eq104914
       grind)
    | exact resolve eq109826 eq104914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104914 eq109826
  have eq117118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq109864
       grind)
    | exact superpose eq109864 eq100
    | exact resolve eq100 eq109864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109864
  have eq117161 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq117118
    | exact resolve eq117118 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117118
  have eq120841 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq117161 eq76091
    | exact resolve eq76091 eq117161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117161
  have eq120858 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq120841
       have r₂ := eq27
       grind)
    | exact resolve eq120841 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120841
  have eq121317 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq120858 eq106726
    | exact resolve eq106726 eq120858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106726 eq120858
  have eq121425 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq121317
  have eq121478 : x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq121425
       have r₂ := eq27
       grind)
    | exact resolve eq121425 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121425
  have eq121523 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq121478
       grind)
    | exact superpose eq121478 eq100
    | exact resolve eq100 eq121478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq121478
  have eq121566 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq121523
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq121523
    | exact resolve eq121523 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121523
  have eq121628 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq76091 eq121566
    | exact resolve eq121566 eq76091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76091 eq121566
  have eq122036 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq121628 eq105145
    | exact resolve eq105145 eq121628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122148 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq122036
  have eq122198 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq122148
       have r₂ := eq27
       grind)
    | exact resolve eq122148 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122148
  have eq122318 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq122198 eq45475
    | exact resolve eq45475 eq122198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45475 eq122198
  have eq122416 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq122318
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq122318
    | exact resolve eq122318 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122318
  have eq122417 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq122416
  have eq123765 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq122417 eq105145
    | exact resolve eq105145 eq122417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105145 eq122417
  have eq123883 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq123765
  have eq124006 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq123883 eq29
    | exact resolve eq29 eq123883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124215 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq28 eq124006
    | exact resolve eq124006 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124006
  have eq124567 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq124215 eq28
    | exact resolve eq28 eq124215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124215
  have eq124866 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq124567
    | exact resolve eq124567 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq124567
  have eq125091 : x = (k x x) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq124866 eq43421
    | exact resolve eq43421 eq124866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43421 eq124866
  have eq125141 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq125091
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq125091
    | exact resolve eq125091 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq125091
  have eq125142 : x = (M.op x x) ∨ x = y := by grind
  clear eq125141
  have eq126461 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq72
       have i₂ := eq125142
       grind)
    | exact superpose eq125142 eq72
    | exact resolve eq72 eq125142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq125142
  have eq126704 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq126461
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq126461
    | exact resolve eq126461 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126461
  have eq128318 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq126704 eq121628
    | exact resolve eq121628 eq126704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121628 eq126704
  have eq128429 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq128318
  have eq142177 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq128429 eq27
    | exact resolve eq27 eq128429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128429
  have eq142452 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq142177
       have r₂ := eq123883
       grind)
    | exact resolve eq142177 eq123883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123883 eq142177
  have eq143194 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq142452 eq29
    | exact resolve eq29 eq142452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq142452
  have eq143408 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq143194
    | exact resolve eq143194 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq143194
  have eq143409 : x = y := by grind
  clear eq143408
  have eq143444 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq143409
       grind)
    | exact superpose eq143409 eq18
    | exact resolve eq18 eq143409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq143445 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq143409
       grind)
    | exact superpose eq143409 eq24
    | exact resolve eq24 eq143409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq143409
  have eq143791 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq143445
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq143445
    | exact resolve eq143445 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq143445
  have eq143841 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq143791 eq26
    | exact resolve eq26 eq143791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq143791
  have eq147752 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq143841 eq71
    | exact resolve eq71 eq143841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq143841
  have eq147986 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq147752
       have i₂ := eq143444
       grind)
    | exact superpose eq143444 eq147752
    | exact resolve eq147752 eq143444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143444 eq147752
  have eq148047 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq147986 eq15
    | exact resolve eq15 eq147986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147986
  have eq148335 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq148047
    | exact resolve eq148047 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq148047
  have eq148433 : False := by grind
  exact eq148433

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_pyx_x_pyx_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq266 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ x) (σ y)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq267 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq276 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq273 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq273 (k X0 X1) (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq273 (M.op X1 X0) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq273 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq273 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq282 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq275 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq275 (M.op X0 X1) X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq275 X0 (M.op X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq275 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq275 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq283 : (σ (M.op x y)) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq266
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq266 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq285 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq282 X0 X1
       have j1 := eq276 X1 X0
       grind)
    | (have r₁ := eq282 X0 X1
       have r₂ := eq276 X0 X1
       grind)
    | (have r₁ := eq282 X1 X0
       have r₂ := eq276 X0 X1
       grind)
    | (have r₁ := eq282 X0 X1
       have r₂ := eq276 (k X1 X0) X1
       grind)
    | exact resolve eq282 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq286 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq283
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq283
    | exact resolve eq283 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq287 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq276 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq287 (σ X0)
       grind)
    | exact superpose eq287 eq15
    | exact resolve eq15 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq298 X0
       have i₂ := eq287 X0
       grind)
    | exact superpose eq287 eq298
    | exact resolve eq298 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287 eq298
  have eq363 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq317 X0
       grind)
    | exact superpose eq317 eq9
    | exact resolve eq9 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq285 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq421 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k X1 (M.op (M.op X0 X1) (M.op X0 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq414 X1 (M.op (M.op X0 X1) (M.op X0 X2))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq414
    | (have j0 := eq414 X1 (M.op (M.op X0 X1) (M.op X0 X2))
       grind)
    | (have r₁ := eq414 X0 (M.op (M.op X0 X0) (M.op X0 X2))
       have r₂ := eq9 X0 X0 X2
       grind)
    | exact resolve eq414 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq422 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq414 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq414
    | (have j0 := eq414 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq414 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq414 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq414 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq425 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq422 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq428 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq425 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq425 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq425 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq450 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq428 X0 (σ X1)
       grind)
    | exact superpose eq428 eq28
    | (have j1 := eq428 X0 (σ X1)
       grind)
    | exact resolve eq28 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : ∀ X0 X1 : G, (k X0 (M.op (M.op X0 X0) (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq421 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq474 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq472 (σ X0) X1
       have i₂ := eq317 X0
       grind)
    | exact superpose eq317 eq472
    | exact resolve eq472 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq516 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq363 X0 (σ X0)
       have i₂ := eq317 X0
       grind)
    | exact superpose eq317 eq363
    | exact resolve eq363 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq532 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq516 X0
       have i₂ := eq317 (M.op X0 X0)
       grind)
    | exact superpose eq317 eq516
    | exact resolve eq516 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq1701 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq450 (σ X0) X1
       grind)
    | exact superpose eq450 eq28
    | (have j1 := eq450 (σ X0) X1
       grind)
    | exact resolve eq28 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq450
  have eq1712 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1701 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1701
    | (have j0 := eq1701 X0 X1
       grind)
    | exact resolve eq1701 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1701
  have eq1726 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1712 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1712
    | (have j0 := eq1712 X0 X1
       grind)
    | exact resolve eq1712 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1712
  have eq1735 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1726 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1726
    | (have j0 := eq1726 X0 X1
       grind)
    | exact resolve eq1726 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726
  have eq1833 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq1735 X1 X0
       grind)
    | exact superpose eq1735 eq11
    | (have j1 := eq1735 X1 X0
       grind)
    | exact resolve eq11 eq1735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1735
  have eq1887 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1833 y x
       grind)
    | exact superpose eq1833 eq16
    | (have j1 := eq1833 y x
       grind)
    | exact resolve eq16 eq1833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1833
  have eq1951 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1887
       have i₂ := eq428 x y
       grind)
    | exact superpose eq428 eq1887
    | (have j1 := eq428 x y
       grind)
    | exact resolve eq1887 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428 eq1887
  have eq1958 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by grind
  clear eq1951
  have eq1959 : x = (k x y) := by grind
  clear eq1958
  have eq2031 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) ∨ x = (M.op x y) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq286
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq286
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq286 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq2032 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ x = (M.op x y) ∨ (k x y) = (M.op y x) := by grind
  clear eq2031
  have eq2033 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (k x y) = (M.op y x) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq2032
       have r₂ := eq12 x y
       grind)
    | exact resolve eq2032 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2032
  have eq2034 : (σ x) = (M.op (σ y) (σ x)) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq2033
       have i₂ := eq1959
       grind)
    | exact superpose eq1959 eq2033
    | exact resolve eq2033 eq1959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2033
  have eq2035 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2034
       have i₂ := eq1959
       grind)
    | exact superpose eq1959 eq2034
    | exact resolve eq2034 eq1959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2034
  have eq2038 : ∀ X0 : G, y = (M.op (M.op x (M.op y X0)) x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq2035
       grind)
    | exact superpose eq2035 eq9
    | exact resolve eq9 eq2035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4021 : y = (M.op (M.op x x) x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2038 x
       have i₂ := eq2035
       grind)
    | exact superpose eq2035 eq2038
    | exact resolve eq2038 eq2035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035 eq2038
  have eq4036 : y = (M.op (M.op x x) x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq4021
  have eq4340 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
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
  have eq4386 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op X0 X1) (M.op X0 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4340 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq4340
    | exact resolve eq4340 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4390 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4)) = (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3))) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4340 (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1 X4
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq4340
    | exact resolve eq4340 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4413 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op X0 X1) (M.op X0 X2))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4340 (M.op (M.op X0 X1) (M.op X0 X2)) X3 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq4340
    | exact resolve eq4340 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4440 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq4340 X0 X1 x
       grind)
    | exact superpose eq4340 eq9
    | exact resolve eq9 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4443 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq532 X0
       have i₂ := eq4340 X0 X0 X0
       grind)
    | exact superpose eq4340 eq532
    | exact resolve eq532 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq4445 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X2)) = (M.op (M.op X0 X0) (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X2)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 (M.op X0 X1) X2 X3
       have i₂ := eq4340 X0 (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X2)) X3) X1
       grind)
    | exact superpose eq4340 eq61
    | exact resolve eq61 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4479 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq4445 X0 X1 x X3
       have i₂ := eq4340 X0 (M.op X0 X1) x
       grind)
    | exact superpose eq4340 eq4445
    | exact resolve eq4445 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4445
  have eq4501 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4413 X0 X1 X2 X3
       have i₂ := eq4340 (M.op X0 X1) (M.op X0 X2) (M.op X0 X2)
       grind)
    | exact superpose eq4340 eq4413
    | exact resolve eq4413 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4413
  have eq4519 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4)) = (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4390 X0 X1 X2 X3 X4
       have i₂ := eq4340 X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)
       grind)
    | exact superpose eq4340 eq4390
    | exact resolve eq4390 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4390
  have eq4523 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X2)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4386 X0 X1 X2 X3
       have i₂ := eq4340 (M.op X0 X1) (M.op X0 X2) (M.op X0 X2)
       grind)
    | exact superpose eq4340 eq4386
    | exact resolve eq4386 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4386
  have eq4530 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X0) X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq4479 x x X3
       have i₂ := eq4340 x x x
       grind)
    | exact superpose eq4340 eq4479
    | exact resolve eq4479 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4479
  have eq4541 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op X0 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4501 X0 X1 X2 X3
       have i₂ := eq4340 X0 X1 X1
       grind)
    | exact superpose eq4340 eq4501
    | exact resolve eq4501 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4501
  have eq4547 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X3)) X4)) = (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X3)) X1) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq4519 X0 X1 x X3 X4
       have i₂ := eq4340 X0 X1 x
       grind)
    | exact superpose eq4340 eq4519
    | exact resolve eq4519 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4519
  have eq4551 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op X0 X2)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4523 X0 X1 X2 X3
       have i₂ := eq4340 X0 X1 X1
       grind)
    | exact superpose eq4340 eq4523
    | exact resolve eq4523 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4523
  have eq4560 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op X0 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4541 X0 X1 X2 X3
       have i₂ := eq4340 X0 X1 X2
       grind)
    | exact superpose eq4340 eq4541
    | exact resolve eq4541 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4541
  have eq4567 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X0 X0) X1) X3)) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op X0 X2)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4551 X0 X1 X2 X3
       have i₂ := eq4340 X0 X1 X2
       grind)
    | exact superpose eq4340 eq4551
    | exact resolve eq4551 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4551
  have eq4580 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op (M.op X0 X0) X1) X3)) = (M.op (M.op (M.op (M.op X0 X0) X1) X1) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq4567 X0 X1 x X3
       have i₂ := eq4560 X0 X1 x X1
       grind)
    | exact superpose eq4560 eq4567
    | exact resolve eq4567 eq4560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4560 eq4567
  have eq4587 : ∀ X0 X1 X3 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq4580 X0 X1 X3
       have i₂ := eq4440 X0 X1
       grind)
    | exact superpose eq4440 eq4580
    | exact resolve eq4580 eq4440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4580
  have eq4589 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4440 (M.op X0 X1) X2
       have i₂ := eq4340 X0 X1 X1
       grind)
    | exact superpose eq4340 eq4440
    | exact resolve eq4440 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4590 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4440 (σ X0) X1
       have i₂ := eq317 X0
       grind)
    | exact superpose eq317 eq4440
    | exact resolve eq4440 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4602 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4440 X0 (M.op X0 X1)
       have i₂ := eq4340 X0 X0 X1
       grind)
    | exact superpose eq4340 eq4440
    | exact resolve eq4440 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4611 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op (M.op X0 X0) X1) X1
       have i₂ := eq4440 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq4440 eq9
    | exact resolve eq9 eq4440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4954 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4602 (M.op (M.op X0 X0) X1) X1
       have i₂ := eq4440 X0 X1
       grind)
    | exact superpose eq4440 eq4602
    | exact resolve eq4602 eq4440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4987 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X0 X0) X0) X2)) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X0) X2)) X3)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 (M.op (M.op X0 X0) X0) (M.op X0 X1) X2 X3
       have i₂ := eq4602 X0 X1
       grind)
    | exact superpose eq4602 eq61
    | exact resolve eq61 eq4602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq4602
  have eq5000 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X0 X0) X0) X2)) = (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X0) X2)) X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4987 X0 X1 X2 x
       have i₂ := eq4547 X0 X0 X2 x
       grind)
    | exact superpose eq4547 eq4987
    | exact resolve eq4987 eq4547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4547 eq4987
  have eq5023 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4954 X0 X1
       have i₂ := eq4589 X0 X1 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq4589 eq4954
    | exact resolve eq4954 eq4589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4589 eq4954
  have eq5039 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X0 X0) X0) X2)) = (M.op (M.op (M.op (M.op X0 X0) X0) X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5000 X0 X1 X2
       have i₂ := eq4530 X0 X2
       grind)
    | exact superpose eq4530 eq5000
    | exact resolve eq5000 eq4530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4530 eq5000
  have eq5058 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (M.op (M.op X0 X0) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5039 X0 X1 X2
       have i₂ := eq4440 X0 X0
       grind)
    | exact superpose eq4440 eq5039
    | exact resolve eq5039 eq4440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5039
  have eq5071 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5058 X0 X1 x
       have i₂ := eq4587 X0 X0 x
       grind)
    | exact superpose eq4587 eq5058
    | exact resolve eq5058 eq4587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4587 eq5058
  have eq5439 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) X2) = (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5023 (M.op X0 X1) X2
       have i₂ := eq4340 X0 X1 X1
       grind)
    | exact superpose eq4340 eq5023
    | exact resolve eq5023 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5454 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X2)) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5023 (M.op X0 X1) (M.op X0 X2)
       have i₂ := eq4340 X0 X1 X2
       grind)
    | exact superpose eq4340 eq5023
    | exact resolve eq5023 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5470 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4611 X0 X1
       have i₂ := eq5023 X0 X1
       grind)
    | (have i₁ := eq4611 X1 X1
       have i₂ := eq5023 X1 X1
       grind)
    | exact superpose eq5023 eq4611
    | exact resolve eq4611 eq5023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4611
  have eq5471 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4440 X0 X1
       have i₂ := eq5023 X0 X1
       grind)
    | (have i₁ := eq4440 X1 X1
       have i₂ := eq5023 X1 X1
       grind)
    | exact superpose eq5023 eq4440
    | exact resolve eq4440 eq5023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5473 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X1
       have i₂ := eq5023 (M.op X0 X1) X1
       grind)
    | exact superpose eq5023 eq9
    | exact resolve eq9 eq5023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5023
  have eq5553 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1)) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5454 X0 X1 X2
       have i₂ := eq4340 X0 X1 X1
       grind)
    | exact superpose eq4340 eq5454
    | exact resolve eq5454 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5454
  have eq5616 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (M.op X0 (M.op X0 X1)) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5471 X0 X1
       have i₂ := eq14 (M.op X0 X1) X0
       grind)
    | exact superpose eq14 eq5471
    | (have j1 := eq14 (M.op X0 X1) X0
       grind)
    | exact resolve eq5471 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5471
  have eq5648 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 (M.op X0 X1)) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq5616 X0 X1
       have j1 := eq12 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq5616 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq5616 X1 X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq5616 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5616
  have eq5670 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq5648 X0 X1
       have j1 := eq276 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq5648 X1 X1
       have r₂ := eq276 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq5648 X0 X1
       have r₂ := eq276 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq5648 X0 X1
       have r₂ := eq276 (M.op X0 (M.op X0 X1)) (k (M.op X0 X1) X0)
       grind)
    | exact resolve eq5648 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276 eq5648
  have eq5681 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5670 X0 X1
       have i₂ := eq5071 X0 X1
       grind)
    | exact superpose eq5071 eq5670
    | exact resolve eq5670 eq5071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5670
  have eq5703 : ∀ X0 X1 : G, (k (σ X0) (M.op (σ (M.op X0 X0)) X1)) = (M.op (M.op (σ (M.op X0 X0)) X1) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5681 (M.op (σ (M.op X0 X0)) X1) X1
       have i₂ := eq4590 X0 X1
       grind)
    | exact superpose eq4590 eq5681
    | exact resolve eq5681 eq4590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4590
  have eq5756 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op (σ X0) X1) X0
       have i₂ := eq5681 (σ X0) X1
       grind)
    | exact superpose eq5681 eq22
    | exact resolve eq22 eq5681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5681
  have eq5789 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ (M.op (σ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5756 X0 X1
       have i₂ := eq317 X0
       grind)
    | exact superpose eq317 eq5756
    | exact resolve eq5756 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5756
  have eq5822 : ∀ X0 X1 : G, (k (σ X0) (M.op (σ (M.op X0 X0)) X1)) = (M.op (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5703 X0 X1
       have i₂ := eq4340 (σ (M.op X0 X0)) X1 X1
       grind)
    | exact superpose eq4340 eq5703
    | exact resolve eq5703 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5703
  have eq5843 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ (M.op (σ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5789 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq5789
    | exact resolve eq5789 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5789
  have eq5865 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) X1) = (k (σ X0) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5822 X0 X1
       have i₂ := eq317 (M.op X0 X0)
       grind)
    | exact superpose eq317 eq5822
    | exact resolve eq5822 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317 eq5822
  have eq5886 : ∀ X0 X1 : G, (k (σ X0) (M.op (σ (M.op X0 X0)) X1)) = (M.op (σ (M.op (M.op X0 X0) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5865 X0 X1
       have i₂ := eq4340 X0 X0 X0
       grind)
    | exact superpose eq4340 eq5865
    | exact resolve eq5865 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5865
  have eq5917 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 (M.op (M.op X0 X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5470 (M.op (M.op X0 X0) X1) X1
       have i₂ := eq4440 X0 X1
       grind)
    | exact superpose eq4440 eq5470
    | exact resolve eq5470 eq4440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5470
  have eq6033 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1)) = (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5917 X0 X1
       have i₂ := eq5553 X0 X1 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq5553 eq5917
    | exact resolve eq5917 eq5553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5553 eq5917
  have eq6059 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1)) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6033 X0 X1
       have i₂ := eq4340 (M.op X0 X0) X1 X1
       grind)
    | exact superpose eq4340 eq6033
    | exact resolve eq6033 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6033
  have eq6076 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6059 X0 X1
       have i₂ := eq4340 X0 X0 X0
       grind)
    | exact superpose eq4340 eq6059
    | exact resolve eq6059 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6059
  have eq6177 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5071 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq5473 X0 X1
       grind)
    | exact superpose eq5473 eq5071
    | exact resolve eq5071 eq5473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5071 eq5473
  have eq6184 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6177 X0 X1
       have i₂ := eq4340 (M.op X0 X1) X1 X1
       grind)
    | exact superpose eq4340 eq6177
    | exact resolve eq6177 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6177
  have eq6227 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6184 X0 X1
       have i₂ := eq9 X0 X1 X1
       grind)
    | exact superpose eq9 eq6184
    | exact resolve eq6184 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6184
  have eq8979 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq4443 x
       have i₂ := eq4036
       grind)
    | exact superpose eq4036 eq4443
    | exact resolve eq4443 eq4036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4036
  have eq9045 : (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq8979
  have eq9625 : (M.op y y) = (k (τ (σ x)) y) := by
    first
    | (have i₁ := eq5843 y (σ x)
       have i₂ := eq9045
       grind)
    | exact superpose eq9045 eq5843
    | exact resolve eq5843 eq9045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5843 eq9045
  have eq9684 : (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq9625
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9625
    | exact resolve eq9625 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9625
  have eq9702 : x = (M.op y y) := by
    first
    | (have i₁ := eq9684
       have i₂ := eq1959
       grind)
    | exact superpose eq1959 eq9684
    | exact resolve eq9684 eq1959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1959 eq9684
  have eq9726 : ∀ X0 : G, y = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq4440 y X0
       have i₂ := eq9702
       grind)
    | exact superpose eq9702 eq4440
    | exact resolve eq4440 eq9702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4440
  have eq9728 : (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq4443 y
       have i₂ := eq9702
       grind)
    | exact superpose eq9702 eq4443
    | exact resolve eq4443 eq9702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4443 eq9702
  have eq10035 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) X1) y) = (M.op (M.op (M.op x X0) (M.op x X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4340 (M.op x X0) X1 X0
       have i₂ := eq9726 X0
       grind)
    | exact superpose eq9726 eq4340
    | exact resolve eq4340 eq9726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9726
  have eq10059 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) X1) y) = (M.op (M.op (M.op x x) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10035 X0 X1
       have i₂ := eq4340 x X0 X0
       grind)
    | exact superpose eq4340 eq10035
    | exact resolve eq10035 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4340 eq10035
  have eq12530 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y))) := by
    first
    | (have i₁ := eq474 (M.op x y) (σ y)
       have i₂ := eq9728
       grind)
    | exact superpose eq9728 eq474
    | exact resolve eq474 eq9728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474 eq9728
  have eq12603 : (σ (M.op x y)) = (M.op (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq12530
       have i₂ := eq5886 (M.op x y) (σ y)
       grind)
    | exact superpose eq5886 eq12530
    | exact resolve eq12530 eq5886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5886 eq12530
  have eq12635 : (σ (M.op x y)) = (M.op (σ (M.op (M.op (M.op x x) y) (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq12603
       have i₂ := eq5439 x y (M.op x y)
       grind)
    | exact superpose eq5439 eq12603
    | exact resolve eq12603 eq5439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5439 eq12603
  have eq12660 : (σ (M.op x y)) = (M.op (σ (M.op (M.op (M.op x x) x) y)) (σ y)) := by
    first
    | (have i₁ := eq12635
       have i₂ := eq6076 x y
       grind)
    | exact superpose eq6076 eq12635
    | exact resolve eq12635 eq6076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6076 eq12635
  have eq12678 : (σ (M.op x y)) = (M.op (σ (M.op (M.op (M.op x x) x) x)) (σ y)) := by
    first
    | (have i₁ := eq12660
       have i₂ := eq10059 x x
       grind)
    | exact superpose eq10059 eq12660
    | exact resolve eq12660 eq10059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10059 eq12660
  have eq12690 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12678
       have i₂ := eq6227 x x
       grind)
    | exact superpose eq6227 eq12678
    | exact resolve eq12678 eq6227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6227 eq12678
  have eq12697 : False := by grind
  exact eq12697

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pyx_x_pxy_Equation2666 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq75 : y ≠ (M.op x y) ∨ x = (M.op y y) ∨ x = (k x y) := by
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
  have eq76 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq110 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq99
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq112
    | exact resolve eq112 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq114
    | exact resolve eq114 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq170 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
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
  have eq497 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4)) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq507 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq521 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) = (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4) (M.op (M.op X0 X1) (M.op X0 X2))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4 X1
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq648 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 X0 X1 X2 (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4)
       have i₂ := eq53 (M.op (M.op X0 X1) (M.op X0 X2)) X0 X3 X4
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq725 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) (σ X1) X2
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq14
    | (have j1 := eq93 X0 X1
       grind)
    | exact resolve eq14 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq731 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq732 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq735 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq731 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq737 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq735 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq735
    | (have j0 := eq735 X0
       grind)
    | exact resolve eq735 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq907 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) y) := by
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
  have eq908 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq516
    | (have j0 := eq516 (σ x) (σ y) X0
       grind)
    | exact resolve eq516 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq912 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4) (M.op (M.op X0 X1) (M.op X0 X2))) = (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq516 (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4 X1
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq516
    | exact resolve eq516 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq920 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x x) X0) := by
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
  have eq921 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq516
    | (have j0 := eq516 (σ x) X0 (σ y)
       grind)
    | exact resolve eq516 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq925 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
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
  have eq926 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X2)) = (M.op (M.op X0 X0) (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X2)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 (M.op X0 X1) X2 X3
       have i₂ := eq516 X0 (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X2)) X3) X1
       grind)
    | exact superpose eq516 eq53
    | exact resolve eq53 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq940 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq926 X0 X1 x X3
       have i₂ := eq516 X0 (M.op X0 X1) x
       grind)
    | exact superpose eq516 eq926
    | exact resolve eq926 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq948 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4) (M.op (M.op X0 X1) (M.op X0 X2))) = (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq912 X0 X1 X2 X3 X4
       have i₂ := eq516 X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)
       grind)
    | exact superpose eq516 eq912
    | exact resolve eq912 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq964 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X0) X3)) := by
    intro X0 X3
    by_contra hcon
    push Not at hcon
    have f964_11 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2)) := by
      intro X0 X1 X2
      grind
    have f964_12 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
      intro X0 X1 X2
      grind
    have f964_20 : (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X0) X3)) := by grind
    have f964_22 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X0) X2)) := by
      intro X0 X2
      first
      | (have i₁ := f964_11 x X2 X2
         have i₂ := f964_12 x x X2
         grind)
      | exact superpose f964_12 f964_11
      | exact resolve f964_11 f964_12
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f964_148 : (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) := by
      first
      | (have i₁ := f964_20
         have i₂ := f964_22 X0 X3
         grind)
      | exact superpose f964_22 f964_20
      | (have r₁ := f964_20
         have r₂ := f964_22 X0 X3
         grind)
      | exact resolve f964_20 f964_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f964_157 : False := by grind
    exact f964_157
  clear eq940
  have eq968 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X3)) X4) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X3)) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq948 X0 X1 x X3 X4
       have i₂ := eq516 X0 X1 x
       grind)
    | exact superpose eq516 eq948
    | exact resolve eq948 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq986 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq925 X0 (M.op X0 X1)
       have i₂ := eq516 X0 X0 X1
       grind)
    | exact superpose eq516 eq925
    | exact resolve eq925 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq987 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq925 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq925 X0 (M.op X0 X0)
       grind)
    | exact superpose eq925 eq925
    | exact resolve eq925 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq991 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 X1 X1 X0
       have i₂ := eq925 (M.op X0 X1) X0
       grind)
    | exact superpose eq925 eq56
    | exact resolve eq56 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq996 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X1
       have i₂ := eq925 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq925 eq14
    | exact resolve eq14 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1011 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq991 X0 X1
       have i₂ := eq516 X0 X1 X1
       grind)
    | exact superpose eq516 eq991
    | exact resolve eq991 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq1094 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq920 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq920
    | (have j0 := eq920 y
       grind)
    | exact resolve eq920 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1128 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1094
       have i₂ := eq907 X0
       grind)
    | exact superpose eq907 eq1094
    | exact resolve eq1094 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1257 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq27 eq921
    | (have j0 := eq921 (σ y)
       grind)
    | exact resolve eq921 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1291 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq908 eq1257
    | exact resolve eq1257 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1392 : (M.op x x) = (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op x x)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq986 (M.op x x) y
       have i₂ := eq1094
       grind)
    | exact superpose eq1094 eq986
    | exact resolve eq986 eq1094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094
  have eq1396 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq209 eq986
    | exact resolve eq986 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1398 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1257 eq986
    | exact resolve eq986 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1402 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq216 eq986
    | exact resolve eq986 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1428 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq1402
       have i₂ := eq925 sF4 (M.op sF4 sF4)
       grind)
    | exact superpose eq925 eq1402
    | exact resolve eq1402 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402
  have eq1432 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1398
       have i₂ := eq925 sF2 (M.op sF2 sF2)
       grind)
    | exact superpose eq925 eq1398
    | exact resolve eq1398 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398
  have eq1434 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq1396
       have i₂ := eq925 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq925 eq1396
    | exact resolve eq1396 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396
  have eq1438 : (M.op x x) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1392
       have i₂ := eq925 x (M.op x x)
       grind)
    | exact superpose eq925 eq1392
    | exact resolve eq1392 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392
  have eq1513 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1428 eq216
    | exact resolve eq216 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1521 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1428 eq516
    | exact resolve eq516 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1527 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) = (k (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by grind
  have eq1529 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq1521 x
       have i₂ := eq516 sF4 sF2 x
       grind)
    | exact superpose eq516 eq1521
    | exact resolve eq1521 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521
  have eq1532 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq1428 eq1529
    | exact resolve eq1529 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529
  have eq1535 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq1434 eq209
    | exact resolve eq209 eq1434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1543 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1434 eq516
    | exact resolve eq516 eq1434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1551 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq1543 x
       have i₂ := eq516 sF0 x x
       grind)
    | exact superpose eq516 eq1543
    | exact resolve eq1543 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543
  have eq1554 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq1434 eq1551
    | exact resolve eq1551 eq1434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551
  have eq1680 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq1428 eq1432
    | exact resolve eq1432 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1432
  have eq1681 : (M.op x x) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq1434 eq1438
    | exact resolve eq1438 eq1434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438
  have eq2214 : ∀ X0 : G, (M.op (M.op (M.op x y) x) X0) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1434 eq1011
    | exact resolve eq1011 eq1434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2216 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1011 (M.op X0 X1) X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq1011
    | exact resolve eq1011 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2218 : x = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | exact superpose eq209 eq1011
    | exact resolve eq1011 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2220 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq216 eq1011
    | exact resolve eq1011 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2224 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1011 (M.op (M.op X0 X0) X0) (M.op X0 X1)
       have i₂ := eq986 X0 X1
       grind)
    | exact superpose eq986 eq1011
    | exact resolve eq1011 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2245 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq925 X0 X1
       have i₂ := eq1011 X0 X1
       grind)
    | (have i₁ := eq925 X1 X1
       have i₂ := eq1011 X1 X1
       grind)
    | exact superpose eq1011 eq925
    | exact resolve eq925 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2298 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2224 X0 X1
       have i₂ := eq996 X0 X0
       grind)
    | exact superpose eq996 eq2224
    | exact resolve eq2224 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996 eq2224
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
  have eq2314 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) y) X0) x) = (M.op (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) X0) := by
    intro X0
    first
    | exact superpose eq2218 eq516
    | exact resolve eq516 eq2218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2317 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) y) X0) x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) y) X0) := by
    intro X0
    first
    | (have i₁ := eq2314 X0
       have i₂ := eq516 sF0 y y
       grind)
    | exact superpose eq516 eq2314
    | exact resolve eq2314 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2314
  have eq2322 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) y) X0) x) := by
    intro X0
    first
    | exact superpose eq209 eq2317
    | exact resolve eq2317 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq2317
  have eq2333 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq2220 eq516
    | exact resolve eq516 eq2220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2336 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq2333 X0
       have i₂ := eq516 sF4 sF3 sF3
       grind)
    | exact superpose eq516 eq2333
    | exact resolve eq2333 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2333
  have eq2341 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq216 eq2336
    | exact resolve eq2336 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2336
  have eq2660 : (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq2220 eq2305
    | exact resolve eq2305 eq2220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2664 : (M.op x x) = (M.op x (M.op x y)) := by
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
  have eq2724 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq2660
       have i₂ := eq516 sF4 sF3 sF3
       grind)
    | exact superpose eq516 eq2660
    | exact resolve eq2660 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2660
  have eq2759 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq216 eq2724
    | exact resolve eq2724 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq2724
  have eq3449 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) y) := by
    intro X1
    first
    | exact superpose eq1128 eq212
    | (have j0 := eq212 y X1
       grind)
    | exact resolve eq212 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq3450 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) y) := by
    intro X1
    first
    | exact superpose eq1434 eq3449
    | exact resolve eq3449 eq1434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3449
  have eq3534 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 X1) X1) := by
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
  have eq3540 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq3450 eq2216
    | exact resolve eq2216 eq3450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3450
  have eq3549 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq2218 eq2216
    | exact resolve eq2216 eq2218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2218
  have eq3560 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq2220 eq2216
    | exact resolve eq2216 eq2220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3595 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X1) X1) X0) := by
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
  have eq3596 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3595 X0 X1
       have i₂ := eq516 (M.op X0 X1) X1 X1
       grind)
    | exact superpose eq516 eq3595
    | exact resolve eq3595 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3595
  have eq3616 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq3560
       have i₂ := eq1011 sF2 sF4
       grind)
    | exact superpose eq1011 eq3560
    | exact resolve eq3560 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3560
  have eq3625 : (M.op (M.op x y) y) = (M.op (M.op x x) (M.op x y)) := by
    first
    | (have i₁ := eq3549
       have i₂ := eq1011 x sF0
       grind)
    | exact superpose eq1011 eq3549
    | exact resolve eq3549 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3549
  have eq3633 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op x (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq1535 eq3540
    | exact resolve eq3540 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535 eq3540
  have eq3637 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3534 X0 X1
       have i₂ := eq1011 X0 (M.op X0 X1)
       grind)
    | exact superpose eq1011 eq3534
    | exact resolve eq3534 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3534
  have eq3651 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3596 X0 X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq3596
    | exact resolve eq3596 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3596
  have eq3663 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq921 eq3616
    | exact resolve eq3616 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921 eq3616
  have eq3668 : (M.op (M.op x y) y) = (M.op (M.op x x) x) := by
    first
    | exact superpose eq920 eq3625
    | exact resolve eq3625 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920 eq3625
  have eq3672 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op (M.op x y) x) X0)) := by
    intro X0
    first
    | exact superpose eq1681 eq3633
    | exact resolve eq3633 eq1681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1681 eq3633
  have eq3674 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3637 X0 X1
       have i₂ := eq516 X0 X0 X1
       grind)
    | exact superpose eq516 eq3637
    | exact resolve eq3637 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3637
  have eq4067 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1291 eq219
    | (have j0 := eq219 (σ y) X1
       grind)
    | exact resolve eq219 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq4068 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1428 eq4067
    | exact resolve eq4067 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4067
  have eq4084 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq4068 eq2216
    | exact resolve eq2216 eq4068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4068
  have eq4090 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq1513 eq4084
    | exact resolve eq4084 eq1513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4084
  have eq4097 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq1680 eq4090
    | exact resolve eq4090 eq1680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1680 eq4090
  have eq4952 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1527
       have i₂ := eq2305 sF4 sF2
       grind)
    | exact superpose eq2305 eq1527
    | exact resolve eq1527 eq2305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1527
  have eq4953 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1428 eq4952
    | exact resolve eq4952 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4952
  have eq5893 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq5913 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5893
  have eq5918 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5913
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq5913
    | exact resolve eq5913 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5913
  have eq5935 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2214 eq3672
    | exact resolve eq3672 eq2214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2214
  have eq5998 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3674 X0 X2
       have i₂ := eq3674 X0 X1
       grind)
    | (have i₁ := eq3674 X1 X1
       have i₂ := eq3674 X1 X1
       grind)
    | exact superpose eq3674 eq3674
    | exact resolve eq3674 eq3674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6002 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq3674 x X0
       have i₂ := eq3668
       grind)
    | exact superpose eq3668 eq3674
    | exact resolve eq3674 eq3668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3668
  have eq6003 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq3663 eq3674
    | exact resolve eq3674 eq3663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3663
  have eq6051 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq986 X0 X2
       have i₂ := eq3674 X0 X1
       grind)
    | (have i₁ := eq986 X1 X1
       have i₂ := eq3674 X1 X1
       grind)
    | exact superpose eq3674 eq986
    | exact resolve eq986 eq3674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986 eq3674
  have eq6337 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) y) (M.op (M.op x X0) X1)) = (M.op (M.op (M.op x X0) (M.op x X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq516 (M.op x X0) X0 X1
       have i₂ := eq6002 X0
       grind)
    | (have i₁ := eq516 (M.op x y) y x
       have i₂ := eq6002 X0
       grind)
    | exact superpose eq6002 eq516
    | exact resolve eq516 eq6002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6349 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) y) (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6337 X0 X1
       have i₂ := eq14 x X0 X0
       grind)
    | exact superpose eq14 eq6337
    | exact resolve eq6337 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6337
  have eq6410 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) X0) X1)) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) X0)) X0) := by
    intro X0 X1
    first
    | exact superpose eq6003 eq516
    | exact resolve eq516 eq6003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6422 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6410 x X1
       have i₂ := eq14 sF2 x x
       grind)
    | exact superpose eq14 eq6410
    | exact resolve eq6410 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6410
  have eq6937 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq737 x
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq737
    | (have j0 := eq737 X0
       have j1 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq737 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq6964 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq6937 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6937
  have eq6973 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq6964
  have eq6987 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6973 X0
       have i₂ := eq987 X0
       grind)
    | exact superpose eq987 eq6973
    | (have j0 := eq6973 X0
       grind)
    | exact resolve eq6973 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6973
  have eq7813 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 (M.op X0 X0))) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq732
  have eq7921 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7813 X0
       have i₂ := eq987 X0
       grind)
    | exact superpose eq987 eq7813
    | (have j0 := eq7813 X0
       grind)
    | exact resolve eq7813 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7813
  have eq8729 : ∀ X0 : G, x = (M.op (M.op (M.op x x) x) (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq5935 eq2245
    | exact resolve eq2245 eq5935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2245 eq5935
  have eq8734 : ∀ X0 : G, x = (M.op (M.op (M.op x y) y) (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq8729 X0
       have i₂ := eq6002 x
       grind)
    | exact superpose eq6002 eq8729
    | exact resolve eq8729 eq6002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6002 eq8729
  have eq9768 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1128 eq499
    | (have j0 := eq499 y X1 X2
       grind)
    | exact resolve eq499 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499 eq1128
  have eq9769 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) x) X1)) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1434 eq9768
    | exact resolve eq9768 eq1434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1434 eq9768
  have eq9770 : ∀ X2 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x x) X2)) y) := by
    intro X2
    first
    | exact superpose eq3672 eq9769
    | exact resolve eq9769 eq3672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3672 eq9769
  have eq9915 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x y) (M.op x X0))) y) := by
    intro X0
    first
    | (have i₁ := eq9770 y
       have i₂ := eq907 X0
       grind)
    | exact superpose eq907 eq9770
    | exact resolve eq9770 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907 eq9770
  have eq9958 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) y) := by
    first
    | (have i₁ := eq9915 x
       have i₂ := eq516 sF0 x (M.op x x)
       grind)
    | exact superpose eq516 eq9915
    | exact resolve eq9915 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9915
  have eq9976 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) y) := by
    first
    | (have i₁ := eq9958
       have i₂ := eq1011 sF0 x
       grind)
    | exact superpose eq1011 eq9958
    | exact resolve eq9958 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9958
  have eq9989 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) x) y) := by
    first
    | exact superpose eq1554 eq9976
    | exact resolve eq9976 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554 eq9976
  have eq10003 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1291 eq500
    | (have j0 := eq500 (σ y) X1 X2
       grind)
    | exact resolve eq500 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500 eq1291
  have eq10004 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1428 eq10003
    | exact resolve eq10003 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10003
  have eq10005 : ∀ X2 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ x)) X2)) (σ y)) := by
    intro X2
    first
    | exact superpose eq4097 eq10004
    | exact resolve eq10004 eq4097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4097 eq10004
  have eq10006 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) X0) X0) y) := by
    intro X0
    first
    | (have i₁ := eq9989
       have i₂ := eq5998 sF0 x x
       grind)
    | (have i₁ := eq9989
       have i₂ := eq5998 sF0 x x
       grind)
    | exact superpose eq5998 eq9989
    | exact resolve eq9989 eq5998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9989
  have eq10051 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) (σ y)) := by
    intro X0
    first
    | exact superpose eq908 eq10005
    | exact resolve eq10005 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908 eq10005
  have eq10094 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq10051 x
       have i₂ := eq516 sF4 sF2 (M.op sF2 x)
       grind)
    | exact superpose eq516 eq10051
    | exact resolve eq10051 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10051
  have eq10112 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq10094
       have i₂ := eq1011 sF4 sF2
       grind)
    | exact superpose eq1011 eq10094
    | exact resolve eq10094 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10094
  have eq10125 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1532 eq10112
    | exact resolve eq10112 eq1532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1532 eq10112
  have eq10139 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10125
       have i₂ := eq5998 sF4 sF2 x
       grind)
    | (have i₁ := eq10125
       have i₂ := eq5998 sF4 x sF2
       grind)
    | exact superpose eq5998 eq10125
    | exact resolve eq10125 eq5998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5998 eq10125
  have eq12638 : ∀ X0 X1 : G, (M.op x x) = (M.op x (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq6349 eq2322
    | exact resolve eq2322 eq6349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2322 eq6349
  have eq12909 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq6422 eq2341
    | exact resolve eq2341 eq6422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341 eq6422
  have eq14730 : ∀ X0 : G, (σ x) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq725 x x X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq725
    | (have j0 := eq725 x x x
       grind)
    | exact resolve eq725 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq725
  have eq14869 : ∀ X0 : G, (σ x) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq14730 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14730
  have eq14904 : ∀ X0 : G, (σ x) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14869 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14869
    | (have j0 := eq14869 X0
       grind)
    | exact resolve eq14869 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14869
  have eq14959 : ∀ X0 : G, (σ x) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14904 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14904
    | (have j0 := eq14904 X0
       grind)
    | exact resolve eq14904 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14904
  have eq15367 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X0 X0) X1) X3)) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X3)) X4)) X1) := by
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
  have eq15480 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X2))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15367 X0 X1 X2 (M.op X0 x)
       have i₂ := eq516 X0 (M.op (M.op (M.op X0 X0) X1) X2) x
       grind)
    | exact superpose eq516 eq15367
    | exact resolve eq15367 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15367
  have eq15528 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15480 X0 X1 X2
       have i₂ := eq14 (M.op X0 X0) X1 (M.op (M.op (M.op X0 X0) X1) X2)
       grind)
    | exact superpose eq14 eq15480
    | exact resolve eq15480 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15480
  have eq15691 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) X3) := by
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
  have eq15801 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) (M.op (M.op X0 X0) (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15691 X0 (M.op X0 X1) X2 X2
       have i₂ := eq56 X0 X0 X1 X2
       grind)
    | exact superpose eq56 eq15691
    | exact resolve eq15691 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq15831 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0) X3) X2
       have i₂ := eq15691 X0 X1 (M.op (M.op (M.op X0 X0) X1) X2) X3
       grind)
    | exact superpose eq15691 eq14
    | exact resolve eq14 eq15691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15691
  have eq15878 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15831 X0 X1 X2 x
       have i₂ := eq2305 (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0) x
       grind)
    | exact superpose eq2305 eq15831
    | exact resolve eq15831 eq2305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15831
  have eq15900 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15801 X0 X1 X2
       have i₂ := eq516 (M.op X0 X0) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq516 eq15801
    | exact resolve eq15801 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15801
  have eq15991 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15878 X0 X1 X2
       have i₂ := eq516 (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0 X0
       grind)
    | exact superpose eq516 eq15878
    | exact resolve eq15878 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15878
  have eq16009 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15900 X0 X1 X2
       have i₂ := eq516 X0 X0 X0
       grind)
    | exact superpose eq516 eq15900
    | exact resolve eq15900 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15900
  have eq16063 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0) (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15991 X0 X1 X2
       have i₂ := eq1011 (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) X2)) X0
       grind)
    | exact superpose eq1011 eq15991
    | exact resolve eq15991 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15991
  have eq16078 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16009 X0 X1 X2
       have i₂ := eq6051 X0 X0 X1
       grind)
    | exact superpose eq6051 eq16009
    | exact resolve eq16009 eq6051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16009
  have eq16105 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16063 X0 X1 X1
       have i₂ := eq2305 (M.op (M.op X0 X0) X1) X1
       grind)
    | exact superpose eq2305 eq16063
    | exact resolve eq16063 eq2305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16063
  have eq16117 : ∀ X0 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X0) X0) X2) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq16078 X0 x X2
       have i₂ := eq516 X0 X0 x
       grind)
    | exact superpose eq516 eq16078
    | exact resolve eq16078 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16078
  have eq16134 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) X0) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1)) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    have f16134_11 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1))) := by
      intro X0 X1
      grind
    have f16134_12 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) (M.op X0 X2)) := by
      intro X0 X1 X2
      grind
    have f16134_20 : (M.op (M.op X0 X0) X1) ≠ (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) X0) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1)) := by grind
    have f16134_22 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) X0) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1)) := by
      intro X0 X1
      first
      | (have i₁ := f16134_11 X0 x
         have i₂ := f16134_12 (M.op X0 X0) x x
         grind)
      | exact superpose f16134_12 f16134_11
      | exact resolve f16134_11 f16134_12
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16134_23 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) (M.op (M.op (M.op X0 X0) X0) X1)) := by
      intro X0 X1
      first
      | (have i₁ := f16134_22 x X1
         have i₂ := f16134_12 x x x
         grind)
      | exact superpose f16134_12 f16134_22
      | exact resolve f16134_22 f16134_12
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16134_177 : (M.op (M.op X0 X0) X1) ≠ (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) (M.op (M.op (M.op X0 X0) X0) X1)) := by
      first
      | (have i₁ := f16134_20
         have i₂ := f16134_12 X0 X0 X0
         grind)
      | exact superpose f16134_12 f16134_20
      | exact resolve f16134_20 f16134_12
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16134_179 : False := by
      first
      | (have r₁ := f16134_177
         have r₂ := f16134_23 X0 X1
         grind)
      | exact resolve f16134_177 f16134_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f16134_179
  clear eq16105
  have eq16150 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) (M.op (M.op (M.op X0 X0) X0) X1)) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    have f16150_11 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) X0) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1)) := by
      intro X0 X1
      grind
    have f16150_12 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) (M.op X0 X2)) := by
      intro X0 X1 X2
      grind
    have f16150_20 : (M.op (M.op X0 X0) X1) ≠ (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) (M.op (M.op (M.op X0 X0) X0) X1)) := by grind
    have f16150_22 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) (M.op (M.op (M.op X0 X0) X0) X1)) := by
      intro X0 X1
      first
      | (have i₁ := f16150_11 x X1
         have i₂ := f16150_12 x x x
         grind)
      | exact superpose f16150_12 f16150_11
      | exact resolve f16150_11 f16150_12
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16150_150 : (M.op (M.op X0 X0) X1) ≠ (M.op (M.op X0 X0) X1) := by
      first
      | (have i₁ := f16150_20
         have i₂ := f16150_22 X0 X1
         grind)
      | exact superpose f16150_22 f16150_20
      | (have r₁ := f16150_20
         have r₂ := f16150_22 X0 X1
         grind)
      | exact resolve f16150_20 f16150_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16150_157 : False := by grind
    exact f16150_157
  clear eq16134
  have eq16566 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X0 X0) X1) X3)) = (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X3)) X4) (M.op (M.op X0 X0) X1)) X4) := by
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
  have eq20190 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3))) := by
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
  have eq20191 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0)) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20190 X0 X1 X2 X3
       have i₂ := eq516 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)
       grind)
    | exact superpose eq516 eq20190
    | exact resolve eq20190 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20190
  have eq20192 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op (M.op X0 X0) X1) X0)) (M.op (M.op (M.op X0 X0) X1) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20191 X0 X1 x X3
       have i₂ := eq516 X0 X1 x
       grind)
    | exact superpose eq516 eq20191
    | exact resolve eq20191 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20191
  have eq20193 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X0) (M.op (M.op (M.op X0 X0) X1) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20192 X0 X1 X3
       have i₂ := eq516 (M.op (M.op X0 X0) X1) X0 X0
       grind)
    | exact superpose eq516 eq20192
    | exact resolve eq20192 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20192
  have eq20194 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op X0 X0) X1)) (M.op (M.op (M.op X0 X0) X1) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20193 X0 X1 X3
       have i₂ := eq1011 (M.op (M.op X0 X0) X1) X0
       grind)
    | exact superpose eq1011 eq20193
    | exact resolve eq20193 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20193
  have eq20307 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 X0) X1))) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20194 (M.op X0 (M.op (M.op (M.op X0 X0) X1) x)) (M.op (M.op X0 X0) X1) (M.op X0 (M.op (M.op (M.op X0 X0) X1) x))
       have i₂ := eq16566 X0 X1 x (M.op X0 (M.op (M.op (M.op X0 X0) X1) x))
       grind)
    | exact superpose eq16566 eq20194
    | exact resolve eq20194 eq16566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16566 eq20194
  have eq20388 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20307 X0 X1 X2
       have i₂ := eq1011 (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 X0) X1))
       grind)
    | exact superpose eq1011 eq20307
    | exact resolve eq20307 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20307
  have eq20508 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20388 X0 X1 X2
       have i₂ := eq2305 (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq2305 eq20388
    | exact resolve eq20388 eq2305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2305 eq20388
  have eq20611 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20508 X0 X1 X2
       have i₂ := eq516 (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))
       grind)
    | exact superpose eq516 eq20508
    | exact resolve eq20508 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20508
  have eq20670 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X2)) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20611 X0 X1 X2
       have i₂ := eq516 X0 (M.op (M.op (M.op X0 X0) X1) X2) (M.op (M.op (M.op X0 X0) X1) X2)
       grind)
    | exact superpose eq516 eq20611
    | exact resolve eq20611 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20611
  have eq20703 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op (M.op X0 X0) X1) X2)) = (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20670 X0 X1 X2
       have i₂ := eq516 (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X2) X1
       grind)
    | exact superpose eq516 eq20670
    | exact resolve eq20670 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20670
  have eq20722 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X1) X2)) = (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X2)) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20703 X0 X1 X2
       have i₂ := eq516 X0 X0 X0
       grind)
    | exact superpose eq516 eq20703
    | exact resolve eq20703 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20703
  have eq31545 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31554 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq31545
    | exact resolve eq31545 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31545
  have eq31561 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq31554
       have r₂ := eq28
       grind)
    | exact resolve eq31554 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31554
  have eq31563 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq31561
    | exact resolve eq31561 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31561
  have eq31565 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  have eq31568 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31563 eq987
    | exact resolve eq987 eq31563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31563
  have eq32731 : (k x y) = (τ (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31565 eq60
    | exact resolve eq60 eq31565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31565
  have eq86580 : (τ (σ x)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31568 eq32731
    | exact resolve eq32731 eq31568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31568 eq32731
  have eq86726 : (τ (σ x)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq86580
  have eq86736 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq86726
    | exact resolve eq86726 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86726
  have eq86738 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq86736
       have r₂ := eq75
       grind)
    | exact resolve eq86736 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq86736
  have eq86742 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq86738
       grind)
    | exact superpose eq86738 eq45
    | exact resolve eq45 eq86738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86755 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq86738
       grind)
    | exact superpose eq86738 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq86738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86738
  have eq86763 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq86755
  have eq86775 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq86763
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq86763
    | exact resolve eq86763 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86763
  have eq86786 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq86742
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq86742
    | exact resolve eq86742 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86742
  have eq86793 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq86775
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq86775
    | exact resolve eq86775 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86775
  have eq86849 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq86786 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq86786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86786
  have eq86866 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq86849
    | exact resolve eq86849 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86849
  have eq86876 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq86866
    | exact resolve eq86866 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86866
  have eq86877 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq86876
  have eq86909 : (k x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq86913 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op x y) X0)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq964 y x
       have i₂ := eq86793
       grind)
    | exact superpose eq86793 eq964
    | exact resolve eq964 eq86793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86915 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq987 y
       have i₂ := eq86793
       grind)
    | exact superpose eq86793 eq987
    | exact resolve eq987 eq86793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987 eq86793
  have eq87007 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq86913 x
       have i₂ := eq12638 y x
       grind)
    | exact superpose eq12638 eq86913
    | exact resolve eq86913 eq12638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86913
  have eq87033 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq87007
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq87007
    | exact resolve eq87007 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87007
  have eq87481 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq110
       have i₂ := eq87033
       grind)
    | exact superpose eq87033 eq110
    | exact resolve eq110 eq87033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87033
  have eq87597 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq87481
  have eq87641 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq87597
    | exact resolve eq87597 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87597
  have eq87837 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5918 eq87641
    | exact resolve eq87641 eq5918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5918
  have eq88315 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq86877 eq964
    | exact resolve eq964 eq86877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86877
  have eq88392 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq12909 eq88315
    | exact resolve eq88315 eq12909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88315
  have eq88402 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq88392
    | exact resolve eq88392 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88392
  have eq88412 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq86909
       grind)
    | exact superpose eq86909 eq45
    | exact resolve eq45 eq86909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq86909
  have eq95574 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq88402 eq925
    | exact resolve eq925 eq88402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88402
  have eq106643 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq88412
       have i₂ := eq86915
       grind)
    | exact superpose eq86915 eq88412
    | exact resolve eq88412 eq86915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86915 eq88412
  have eq106724 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq106643
  have eq106729 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq106724
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq106724
    | exact resolve eq106724 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106724
  have eq106744 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq106729 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq106729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106729
  have eq106762 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq106744
    | exact resolve eq106744 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106744
  have eq106772 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq106762
    | exact resolve eq106762 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106762
  have eq106773 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq106772
  have eq107820 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq106773 eq964
    | exact resolve eq964 eq106773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964 eq106773
  have eq107904 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12909 eq107820
    | exact resolve eq107820 eq12909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12909 eq107820
  have eq107916 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq107904
    | exact resolve eq107904 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107904
  have eq184547 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) (M.op (M.op (M.op X0 X0) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16150 X0 X1
       have i₂ := eq16117 X0 X1
       grind)
    | exact superpose eq16117 eq16150
    | exact resolve eq16150 eq16117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16117 eq16150
  have eq215853 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq107916 eq87837
    | exact resolve eq87837 eq107916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87837 eq107916
  have eq216007 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq215853
  have eq216078 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq216007
       have r₂ := eq28
       grind)
    | exact resolve eq216007 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216007
  have eq216121 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq216078 eq76
    | (have r₁ := eq76
       have r₂ := eq216078
       grind)
    | exact resolve eq76 eq216078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq216174 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ y) X0) X0) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq216078 eq10139
    | exact resolve eq10139 eq216078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10139
  have eq216186 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq216078
  have eq216187 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq216121
  have eq216188 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq216174 x
       have i₂ := eq3651 sF3 x
       grind)
    | exact superpose eq3651 eq216174
    | exact resolve eq216174 eq3651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216174
  have eq216266 : (σ x) = (M.op (M.op (k (σ x) (σ x)) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq216188 eq14959
    | exact resolve eq14959 eq216188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14959
  have eq216278 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq216188 eq925
    | exact resolve eq925 eq216188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925 eq216188
  have eq216387 : (σ x) = (M.op (M.op (k (σ x) (σ x)) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq216266
       have r₂ := eq216186
       grind)
    | exact resolve eq216266 eq216186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216186 eq216266
  have eq245893 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (k (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq216387 eq2216
    | exact resolve eq2216 eq216387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216387
  have eq245921 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (k (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6003 eq245893
    | exact resolve eq245893 eq6003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245893
  have eq265259 : (k (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq245921 eq2216
    | exact resolve eq2216 eq245921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245921
  have eq265283 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq265259
       have i₂ := eq2216 sF4 sF3
       grind)
    | exact superpose eq2216 eq265259
    | exact resolve eq265259 eq2216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265259
  have eq399642 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X3)) X4) = (M.op (M.op (M.op X0 X0) X4) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq968 X0 X1 X3 X4
       have i₂ := eq15528 X0 X1 X3
       grind)
    | exact superpose eq15528 eq968
    | exact resolve eq968 eq15528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968 eq15528
  have eq399643 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X3)) X4) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq399642 X0 X1 X3 X4
       have i₂ := eq516 (M.op X0 X0) X4 X1
       grind)
    | exact superpose eq516 eq399642
    | exact resolve eq399642 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399642
  have eq399644 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X3)) X4) = (M.op (M.op (M.op X0 X0) X0) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq399643 X0 X1 X3 X4
       have i₂ := eq516 X0 X0 X0
       grind)
    | exact superpose eq516 eq399643
    | exact resolve eq399643 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516 eq399643
  have eq475124 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq216187 eq60
    | exact resolve eq60 eq216187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq216187
  have eq475212 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq475124
    | exact resolve eq475124 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475124
  have eq475308 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq475212 eq216278
    | exact resolve eq216278 eq475212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216278 eq475212
  have eq475440 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by grind
  clear eq475308
  have eq475544 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq27 eq475440
    | exact resolve eq475440 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475440
  have eq475545 : x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq475544
  have eq475662 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq475545
       grind)
    | exact superpose eq475545 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq475545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475545
  have eq475692 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq475662
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq475662
    | exact resolve eq475662 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475662
  have eq475693 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq475692
  have eq475731 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq475693
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq475693
    | exact resolve eq475693 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475693
  have eq475732 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq475731
  have eq476062 : (M.op x y) = (M.op x (M.op (M.op x y) y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq184547 y y
       have i₂ := eq475732
       grind)
    | exact superpose eq475732 eq184547
    | exact resolve eq184547 eq475732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475732
  have eq476127 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq476062
       have i₂ := eq12638 y y
       grind)
    | exact superpose eq12638 eq476062
    | exact resolve eq476062 eq12638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476062
  have eq476171 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq476127
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq476127
    | exact resolve eq476127 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476127
  have eq476775 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq110
       have i₂ := eq476171
       grind)
    | exact superpose eq476171 eq110
    | exact resolve eq110 eq476171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476171
  have eq477009 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq476775
  have eq477079 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq477009
    | exact resolve eq477009 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477009
  have eq480513 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq477079 eq265283
    | exact resolve eq265283 eq477079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265283 eq477079
  have eq480638 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq480513
  have eq480665 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq480638
       have r₂ := eq28
       grind)
    | exact resolve eq480638 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480638
  have eq480677 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq480665 eq28
    | exact resolve eq28 eq480665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480688 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq480665 eq1513
    | exact resolve eq1513 eq480665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480972 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1257 eq480688
    | exact resolve eq480688 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257 eq480688
  have eq480993 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1428 eq480972
    | exact resolve eq480972 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428 eq480972
  have eq487320 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq480993 eq4953
    | exact resolve eq4953 eq480993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4953 eq480993
  have eq493192 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq480665 eq487320
    | exact resolve eq487320 eq480665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480665
  have eq493243 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq493192
  have eq493749 : (τ (σ x)) = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq493243 eq50
    | exact resolve eq50 eq493243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq493763 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq493243 eq87641
    | exact resolve eq87641 eq493243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87641 eq493243
  have eq493925 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq493763
  have eq493944 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq493925
       have r₂ := eq480677
       grind)
    | exact resolve eq493925 eq480677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493925
  have eq493948 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq493749
    | exact resolve eq493749 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493749
  have eq494706 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq493944 eq487320
    | exact resolve eq487320 eq493944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487320 eq493944
  have eq494707 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq494706
  have eq504751 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq493948
       grind)
    | exact superpose eq493948 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq493948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493948
  have eq504778 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq504751
  have eq508430 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq494707 eq115
    | exact resolve eq115 eq494707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq494707
  have eq508481 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq508430
  have eq508502 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq508481
       have r₂ := eq480677
       grind)
    | exact resolve eq508481 eq480677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480677 eq508481
  have eq519900 : (M.op x y) = (M.op x (M.op (M.op x y) y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq184547 y y
       have i₂ := eq508502
       grind)
    | exact superpose eq508502 eq184547
    | exact resolve eq184547 eq508502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184547 eq508502
  have eq519967 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq519900
       have i₂ := eq12638 y y
       grind)
    | exact superpose eq12638 eq519900
    | exact resolve eq519900 eq12638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519900
  have eq520009 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq519967
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq519967
    | exact resolve eq519967 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519967
  have eq529443 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq504778
       have i₂ := eq520009
       grind)
    | exact superpose eq520009 eq504778
    | exact resolve eq504778 eq520009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504778 eq520009
  have eq529635 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq529443
  have eq530649 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq529635 eq21
    | exact resolve eq21 eq529635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530800 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq529635 eq2664
    | exact resolve eq2664 eq529635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2664
  have eq530882 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op y X0) X0) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq529635 eq10006
    | exact resolve eq10006 eq529635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10006
  have eq530911 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq529635
  have eq530914 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq530882 x
       have i₂ := eq3651 y x
       grind)
    | exact superpose eq3651 eq530882
    | exact resolve eq530882 eq3651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530882
  have eq530947 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq530800
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq530800
    | exact resolve eq530800 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530800
  have eq531069 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq530649
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq530649
    | exact resolve eq530649 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530649
  have eq532010 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq531069 eq2759
    | exact resolve eq2759 eq531069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2759
  have eq533036 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6987 x
       have i₂ := eq530914
       grind)
    | exact superpose eq530914 eq6987
    | (have j0 := eq6987 x
       grind)
    | exact resolve eq6987 eq530914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6987 eq530914
  have eq533169 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq533036
       have r₂ := eq530911
       grind)
    | exact resolve eq533036 eq530911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530911 eq533036
  have eq533201 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq533169
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq533169
    | exact resolve eq533169 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533169
  have eq533213 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq533201
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq533201
    | exact resolve eq533201 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533201
  have eq533218 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq533213
    | exact resolve eq533213 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533213
  have eq533221 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq533218
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq533218
    | exact resolve eq533218 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533218
  have eq533226 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq530947
       grind)
    | exact superpose eq530947 eq110
    | exact resolve eq110 eq530947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq530947
  have eq533460 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq533226
  have eq533538 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq533460
    | exact resolve eq533460 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533460
  have eq533812 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X1) X2)) = (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20722 X0 X1 X2
       have i₂ := eq399644 X0 X1 X2 (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2))
       grind)
    | exact superpose eq399644 eq20722
    | exact resolve eq20722 eq399644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20722 eq399644
  have eq533813 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq533812 X0 X1 X2
       have i₂ := eq6051 X0 X0 (M.op (M.op (M.op X0 X0) X1) X2)
       grind)
    | exact superpose eq6051 eq533812
    | exact resolve eq533812 eq6051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6051 eq533812
  have eq582974 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq533221 eq3651
    | exact resolve eq3651 eq533221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3651 eq533221
  have eq583071 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6003 eq582974
    | exact resolve eq582974 eq6003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6003 eq582974
  have eq584550 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq531069 eq583071
    | exact resolve eq583071 eq531069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531069 eq583071
  have eq584767 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq584550
  have eq584820 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq584767
       have r₂ := eq28
       grind)
    | exact resolve eq584767 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584767
  have eq584868 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq584820 eq532010
    | exact resolve eq532010 eq584820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532010 eq584820
  have eq584949 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq584868
  have eq587450 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq608687 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq587450 eq533538
    | exact resolve eq533538 eq587450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533538 eq587450
  have eq608743 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq608687
  have eq617628 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq608743 eq584949
    | exact resolve eq584949 eq608743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584949 eq608743
  have eq617846 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq617628
  have eq617944 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq617846 eq29
    | exact resolve eq29 eq617846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq617846
  have eq618859 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq617944
    | exact resolve eq617944 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq617944
  have eq618860 : x = (M.op x y) := by grind
  clear eq618859
  have eq618864 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq618860 eq21
    | exact resolve eq21 eq618860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq619095 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op x X0) x)) := by
    intro X0
    first
    | exact superpose eq618860 eq8734
    | exact resolve eq8734 eq618860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8734
  have eq619273 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op x X0) x)) := by
    intro X0
    first
    | (have i₁ := eq619095 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq619095
    | (have j0 := eq619095 X0
       grind)
    | exact resolve eq619095 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619095
  have eq619438 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq618864
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq618864
    | exact resolve eq618864 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618864
  have eq619474 : ∀ X0 : G, x = (M.op x (M.op (M.op x X0) x)) := by
    intro X0
    first
    | exact superpose eq618860 eq619273
    | exact resolve eq619273 eq618860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619273
  have eq619515 : x = (M.op x x) := by
    first
    | (have i₁ := eq619474 x
       have i₂ := eq12638 x x
       grind)
    | exact superpose eq12638 eq619474
    | exact resolve eq619474 eq12638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619474
  have eq619588 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq619438 eq27
    | exact resolve eq27 eq619438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq619649 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq619438 eq1513
    | exact resolve eq1513 eq619438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513
  have eq620428 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq7921 x
       have i₂ := eq619515
       grind)
    | exact superpose eq619515 eq7921
    | exact resolve eq7921 eq619515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7921
  have eq620521 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq620428
  have eq620522 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq620521
  have eq620587 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq620522
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq620522
    | exact resolve eq620522 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620522
  have eq620688 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq619438 eq620587
    | exact resolve eq620587 eq619438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620587
  have eq634414 : (M.op (M.op (σ (M.op x y)) (σ y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq619649 eq2216
    | exact resolve eq2216 eq619649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2216
  have eq634457 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq634414
       have i₂ := eq1011 sF1 sF3
       grind)
    | exact superpose eq1011 eq634414
    | exact resolve eq634414 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011 eq634414
  have eq634494 : (M.op (σ (M.op x y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq620688 eq634457
    | exact resolve eq634457 eq620688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620688 eq634457
  have eq634521 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq619588 eq634494
    | exact resolve eq634494 eq619588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634494
  have eq634576 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq634521 eq619649
    | exact resolve eq619649 eq634521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619649
  have eq634596 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq634521 eq95574
    | exact resolve eq95574 eq634521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95574
  have eq634684 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq634521 eq634596
    | exact resolve eq634596 eq634521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634596
  have eq634685 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq634684
  have eq634732 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq619438 eq634685
    | exact resolve eq634685 eq619438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634685
  have eq634766 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq634732
       have r₂ := eq28
       grind)
    | exact resolve eq634732 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634732
  have eq634881 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq634576 eq2220
    | exact resolve eq2220 eq634576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2220
  have eq635087 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq619438 eq634881
    | exact resolve eq634881 eq619438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634881
  have eq653953 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op x X0) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq533813 y X1 x
       have i₂ := eq634766
       grind)
    | exact superpose eq634766 eq533813
    | exact resolve eq533813 eq634766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533813 eq634766
  have eq654097 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op x X0) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq653953 X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq653953
    | (have j0 := eq653953 X0 X1
       grind)
    | exact resolve eq653953 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq653953
  have eq654152 : ∀ X0 X1 : G, y = (M.op x (M.op (M.op x X0) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq618860 eq654097
    | exact resolve eq654097 eq618860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618860 eq654097
  have eq654196 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq654152 x x
       have i₂ := eq12638 x x
       grind)
    | exact superpose eq12638 eq654152
    | exact resolve eq654152 eq12638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12638 eq654152
  have eq654224 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq654196
       have i₂ := eq619515
       grind)
    | exact superpose eq619515 eq654196
    | exact resolve eq654196 eq619515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619515 eq654196
  have eq654495 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq654224 eq635087
    | exact resolve eq635087 eq654224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635087 eq654224
  have eq654499 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq619588 eq654495
    | exact resolve eq654495 eq619588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619588 eq654495
  have eq654586 : x = y := by
    first
    | (have r₁ := eq654499
       have r₂ := eq28
       grind)
    | exact resolve eq654499 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654499
  have eq654659 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq654586
       grind)
    | exact superpose eq654586 eq25
    | exact resolve eq25 eq654586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq654586
  have eq655488 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq654659
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq654659
    | exact resolve eq654659 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq654659
  have eq655676 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq619438 eq655488
    | exact resolve eq655488 eq619438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619438 eq655488
  have eq657717 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq655676 eq634576
    | exact resolve eq634576 eq655676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634576 eq655676
  have eq657738 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq634521 eq657717
    | exact resolve eq657717 eq634521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634521 eq657717
  have eq657971 : False := by grind
  exact eq657971

/-- `Equation2683`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation2683 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2683 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2683.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq73 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq276 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq73 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq73 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq73 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq73 X0 X0
       grind)
    | exact resolve eq13 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq303 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq276 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq304 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq303 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq306 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq304 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq304
    | (have j0 := eq304 X0 X1
       grind)
    | exact resolve eq304 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq309 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq306 X0 X1
       have j1 := eq300 X1 X0
       grind)
    | (have r₁ := eq306 X1 X0
       have r₂ := eq300 X0 X1
       grind)
    | (have r₁ := eq306 X1 (k X0 X1)
       have r₂ := eq300 X0 X1
       grind)
    | (have r₁ := eq306 X1 X1
       have r₂ := eq300 X1 X1
       grind)
    | exact resolve eq306 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300 eq306
  have eq703 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq309 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq309
    | exact resolve eq309 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq309 y x
       grind)
    | exact superpose eq309 eq16
    | (have j1 := eq309 y x
       grind)
    | exact resolve eq16 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq736 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq703 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq703
    | (have j0 := eq703 X0 X1
       grind)
    | exact resolve eq703 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq703
  have eq742 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq736 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq736
    | exact resolve eq736 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq858 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq742 (τ X0) X1
       grind)
    | exact superpose eq742 eq18
    | (have j1 := eq742 (τ X0) X1
       grind)
    | exact resolve eq18 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq742
  have eq1070 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq858 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq858
    | exact resolve eq858 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq1116 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1070 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1070
    | (have j0 := eq1070 X0 X1
       grind)
    | exact resolve eq1070 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070
  have eq1176 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq711
       have i₂ := eq1116 x y
       grind)
    | exact superpose eq1116 eq711
    | (have j1 := eq1116 (σ x) (σ y)
       grind)
    | (have r₁ := eq711
       have r₂ := eq1116 x y
       grind)
    | exact resolve eq711 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1177 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1176
  have eq1270 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1177
  have eq1341 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq711
       have i₂ := eq1270
       grind)
    | exact superpose eq1270 eq711
    | exact resolve eq711 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq1270
  have eq1342 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1341
  have eq1343 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1342
  have eq1415 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1343
  have eq1441 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1415
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1415
    | exact resolve eq1415 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415
  have eq1576 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1441
       grind)
    | exact superpose eq1441 eq16
    | exact resolve eq16 eq1441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441
  have eq1600 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1576
       have i₂ := eq1116 x y
       grind)
    | exact superpose eq1116 eq1576
    | (have j1 := eq1116 x y
       grind)
    | (have r₁ := eq1576
       have r₂ := eq1116 x y
       grind)
    | exact resolve eq1576 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1601 : x = (M.op y y) := by grind
  clear eq1600
  have eq1648 : (M.op x y) = (k x y) := by grind
  clear eq1601
  have eq1773 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1576
       have i₂ := eq1648
       grind)
    | exact superpose eq1648 eq1576
    | exact resolve eq1576 eq1648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1576 eq1648
  have eq1776 : False := by grind
  exact eq1776

/-- `Equation2683`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation2683 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2683 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2683.models_iff G M).mp hM
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
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq45 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq45 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq45 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq49 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq47 (σ X0)
       grind)
    | exact superpose eq47 eq15
    | exact resolve eq15 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq47 (τ X0)
       grind)
    | exact superpose eq47 eq18
    | exact resolve eq18 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq52 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq51 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq51
    | exact resolve eq51 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq54 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq49 X0
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq49
    | exact resolve eq49 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq52 X0
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq52
    | exact resolve eq52 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq52
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 X1
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq71
    | (have j0 := eq71 X0 X1
       grind)
    | exact resolve eq71 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1
       have i₂ := eq54 X1
       grind)
    | exact superpose eq54 eq76
    | (have j0 := eq76 X0 X1
       grind)
    | exact resolve eq76 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq106 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq238 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq78
    | (have j0 := eq78 X0 X1
       grind)
    | exact resolve eq78 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq271 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq238 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq238
    | (have j0 := eq238 X0 X1
       grind)
    | exact resolve eq238 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq238
  have eq275 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq271 X0 X1
       have j1 := eq106 X1 X0
       grind)
    | (have r₁ := eq271 X0 X0
       have r₂ := eq106 X0 X1
       grind)
    | exact resolve eq271 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq271
  have eq279 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq275 X0 X1
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq275
    | (have j0 := eq275 X0 X1
       grind)
    | exact resolve eq275 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq275
  have eq920 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq279 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq279
    | exact resolve eq279 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq1001 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq920 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq920 X0 X1
       grind)
    | exact superpose eq920 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq920 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq920 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq920 X0 X1
       grind)
    | exact resolve eq13 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1031 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1001 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1039 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1031 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq1031 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1031 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031
  have eq1111 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1039 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq1115 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1111 X0 X1
       have j1 := eq920 X1 X0
       grind)
    | (have r₁ := eq1111 X0 X0
       have r₂ := eq920 X0 X0
       grind)
    | (have r₁ := eq1111 X1 X0
       have r₂ := eq920 X0 X1
       grind)
    | exact resolve eq1111 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920 eq1111
  have eq1236 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1115 (σ X0) (σ X1)
       grind)
    | exact superpose eq1115 eq15
    | exact resolve eq15 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1257 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1236 X0 X1
       have i₂ := eq1115 X0 X1
       grind)
    | exact superpose eq1115 eq1236
    | exact resolve eq1236 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115 eq1236
  have eq1790 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1257 x y
       grind)
    | exact superpose eq1257 eq16
    | (have r₁ := eq16
       have r₂ := eq1257 x y
       grind)
    | exact resolve eq16 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257
  have eq1829 : False := by grind
  exact eq1829
