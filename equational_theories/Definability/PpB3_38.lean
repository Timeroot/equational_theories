import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyx_pyx_pxy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq339 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq83 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq12 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq340 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq83 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq363 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq340 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq370 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq363 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq363 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq363 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq363 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq371 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq339 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq339 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq339 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq378 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq370 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq370
    | (have j0 := eq370 X0 X1
       grind)
    | exact resolve eq370 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq379 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq378 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq380 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq371 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq371
    | (have j0 := eq371 X0 X1
       grind)
    | exact resolve eq371 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq381 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq380 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq384 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq381 X0 X1
       have j1 := eq379 X0 X1
       grind)
    | (have r₁ := eq381 X0 X1
       have r₂ := eq379 X0 X1
       grind)
    | exact resolve eq381 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq381
  have eq385 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq384 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq384
    | exact resolve eq384 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq384 x y
       grind)
    | exact superpose eq384 eq16
    | exact resolve eq16 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq481 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq385 X0 (τ X1)
       grind)
    | exact superpose eq385 eq17
    | exact resolve eq17 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq385
  have eq499 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq481 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq481
    | exact resolve eq481 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq507 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq499 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq499
    | exact resolve eq499 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq519 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq397
       have i₂ := eq507 x y
       grind)
    | exact superpose eq507 eq397
    | exact resolve eq397 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq507
  have eq520 : False := by grind
  exact eq520

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_x_pyx_x_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq13
    | (have j0 := eq13 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X1) X0
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq72 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq306 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
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
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq307 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq306 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq306
    | (have j0 := eq306 (σ X0) (σ X1)
       grind)
    | exact resolve eq306 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq468 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq307 X1 X0
       have i₂ := eq306 X1 X0
       grind)
    | exact superpose eq306 eq307
    | (have j0 := eq307 X1 X0
       have j1 := eq306 (σ X1) (σ X0)
       grind)
    | exact resolve eq307 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2980 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq468 x y
       grind)
    | exact superpose eq468 eq16
    | (have j1 := eq468 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq468 x y
       grind)
    | exact resolve eq16 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq3004 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2980
  have eq3017 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3004
       grind)
    | exact superpose eq3004 eq16
    | exact resolve eq16 eq3004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3028 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq72 (σ x) (σ y)
       have i₂ := eq3004
       grind)
    | exact superpose eq3004 eq72
    | exact resolve eq72 eq3004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3036 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3028
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3028
    | exact resolve eq3028 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3028
  have eq3040 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq306 eq3036
    | (have j1 := eq306 y x
       grind)
    | exact resolve eq3036 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3036
  have eq3042 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq3040
       have r₂ := eq3017
       grind)
    | exact resolve eq3040 eq3017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3040
  have eq3050 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq3042
       grind)
    | exact superpose eq3042 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq3042
       grind)
    | exact resolve eq12 eq3042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3042
  have eq3066 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq3050
  have eq3071 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3066
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3066
    | exact resolve eq3066 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3066
  have eq3076 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3004 eq3071
    | exact resolve eq3071 eq3004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3004 eq3071
  have eq3078 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq306 eq3076
    | (have j1 := eq306 y x
       grind)
    | exact resolve eq3076 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq3076
  have eq3079 : y = (M.op x y) := by
    first
    | (have r₁ := eq3078
       have r₂ := eq3017
       grind)
    | exact resolve eq3078 eq3017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3017 eq3078
  have eq3080 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3079
       grind)
    | exact superpose eq3079 eq16
    | exact resolve eq16 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3091 : y = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq72 x y
       have i₂ := eq3079
       grind)
    | exact superpose eq3079 eq72
    | exact resolve eq72 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq3225 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq307 y x
       have i₂ := eq3091
       grind)
    | exact superpose eq3091 eq307
    | (have j0 := eq307 y x
       grind)
    | exact resolve eq307 eq3091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3091
  have eq3228 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq3225
  have eq3233 : y = (M.op y x) := by
    first
    | (have r₁ := eq3228
       have r₂ := eq3080
       grind)
    | exact resolve eq3228 eq3080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3228
  have eq3238 : y ≠ y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq3233
       grind)
    | exact superpose eq3233 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3233
       grind)
    | exact resolve eq12 eq3233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3233
  have eq3254 : (M.op x y) = (k y x) := by grind
  clear eq3238
  have eq3258 : y = (k y x) := by
    first
    | (have i₁ := eq3254
       have i₂ := eq3079
       grind)
    | exact superpose eq3079 eq3254
    | exact resolve eq3254 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3079 eq3254
  have eq3289 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq307 y x
       have i₂ := eq3258
       grind)
    | exact superpose eq3258 eq307
    | (have j0 := eq307 y x
       grind)
    | exact resolve eq307 eq3258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307 eq3258
  have eq3292 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3289
  have eq3297 : False := by grind
  exact eq3297

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_x_pxy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X2) = (M.op (M.op (M.op X0 X3) X3) (M.op (M.op (M.op X0 X1) X2) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op (M.op X0 X1) X2) X2) X0 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X1)
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 (M.op (M.op X0 X1) X2)
       have i₂ := eq63 (M.op X0 X1) X2
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq74 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op (σ X0) X1)
       have i₂ := eq71 (σ X0) X1
       grind)
    | exact superpose eq71 eq28
    | exact resolve eq28 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq77 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq74
    | exact resolve eq74 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq225 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X0 X1) X2) X2) = (M.op X0 (M.op (M.op (M.op X0 X1) X2) X2)) ∨ (M.op X0 (M.op (M.op (M.op X0 X1) X2) X2)) = (k X0 (M.op (M.op (M.op X0 X1) X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X0) = X0 ∨ (M.op (M.op X0 X1) X0) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq13
    | (have j0 := eq13 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X1) X0
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k (M.op X0 X1) X0) ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq227 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq230 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X0 X1) X2) X2)) = (k X0 (M.op (M.op (M.op X0 X1) X2) X2)) ∨ (M.op (M.op (M.op X0 X1) X2) X2) = (M.op X0 (M.op (M.op (M.op X0 X1) X2) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq225 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq406 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq416 : ∀ X0 X1 : G, (M.op (τ (M.op (σ X0) X1)) X0) = X0 ∨ (M.op (τ (M.op (σ X0) X1)) X0) = X0 ∨ (τ (M.op (σ X0) X1)) = (M.op X0 (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq14 X0 (τ (M.op (σ X0) X1))
       grind)
    | exact superpose eq14 eq77
    | (have j1 := eq14 X0 (τ (M.op (σ X0) X1))
       grind)
    | exact resolve eq77 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (M.op X0 (τ (M.op (σ X0) X1))) ∨ (M.op (τ (M.op (σ X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq416 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq1023 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X3) X3) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X2) X4) X4) (M.op (M.op X0 X3) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 (M.op (M.op (M.op X0 X1) X2) X2) X0 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq6521 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq406 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq406
    | (have j0 := eq406 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq406 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6522 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq406 X0 (M.op X0 X1)
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq406
    | (have j0 := eq406 X0 (M.op X0 X1)
       grind)
    | exact resolve eq406 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq6680 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq6522 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6522
  have eq9669 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (M.op (σ (M.op X0 X1)) (σ X0)) = (k (σ (M.op X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ (M.op X0 X1)) (σ X0)
       have i₂ := eq6680 X0 X1
       grind)
    | exact superpose eq6680 eq13
    | (have j0 := eq13 (σ (M.op X0 X1)) (σ X0)
       have j1 := eq6680 X0 X1
       grind)
    | (have r₁ := eq13 (σ (M.op X0 X1)) (σ X0)
       have r₂ := eq6680 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ (M.op X0 X1))
       have r₂ := eq6680 X0 X1
       grind)
    | exact resolve eq13 eq6680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6680
  have eq9695 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (M.op (σ (M.op X0 X1)) (σ X0)) = (k (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq9669 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9669
  have eq9696 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (M.op (σ (M.op X0 X1)) (σ X0)) = (k (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq9695 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9695
  have eq9700 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X1)) (σ X0)) = (σ (k (M.op X0 X1) X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9696 X0 X1
       have i₂ := eq15 (M.op X0 X1) X0
       grind)
    | exact superpose eq15 eq9696
    | (have j0 := eq9696 X0 X1
       grind)
    | exact resolve eq9696 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9696
  have eq9709 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ X0) (τ (M.op X0 X1))) ∨ (τ X0) = (M.op (τ (M.op X0 X1)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq433 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq433
    | exact resolve eq433 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11922 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X2) = (M.op (M.op X0 X1) (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1023 X0 X1 (M.op X0 X1) X2 (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq1023
    | exact resolve eq1023 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq12066 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11922 (M.op (M.op X0 X1) X0) X1 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq11922
    | exact resolve eq11922 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11922
  have eq12218 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (τ (M.op (σ X0) X1)) X0) X2) X0) = X0 ∨ (M.op (τ (M.op (σ X0) X1)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12066 X0 (τ (M.op (σ X0) X1)) X2
       have i₂ := eq433 X0 X1
       grind)
    | exact superpose eq433 eq12066
    | (have j1 := eq433 X0 X1
       grind)
    | exact resolve eq12066 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74249 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6521 x y
       grind)
    | exact superpose eq6521 eq16
    | (have j1 := eq6521 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq6521 x y
       grind)
    | exact resolve eq16 eq6521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6521
  have eq74480 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq74249
  have eq74601 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X1)) (σ X0)) = (σ (k (M.op X0 X1) X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq9700 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9700
  have eq100171 : x = (k x (τ (σ y))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq77 x (σ y)
       have i₂ := eq74480
       grind)
    | exact superpose eq74480 eq77
    | exact resolve eq77 eq74480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74480
  have eq100311 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq100171
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq100171
    | exact resolve eq100171 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100171
  have eq100327 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq100311
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq100311
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq100311
       have r₂ := eq12 y x
       grind)
    | exact resolve eq100311 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100311
  have eq100332 : y = (k y (τ (σ x))) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq77 y (σ x)
       have i₂ := eq100327
       grind)
    | exact superpose eq100327 eq77
    | exact resolve eq77 eq100327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100333 : (τ (σ x)) = (M.op y (τ (σ x))) ∨ y = (M.op (τ (σ x)) y) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq433 y (σ x)
       have i₂ := eq100327
       grind)
    | exact superpose eq100327 eq433
    | exact resolve eq433 eq100327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433 eq100327
  have eq100468 : x = (M.op y x) ∨ y = (M.op (τ (σ x)) y) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq100333
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq100333
    | exact resolve eq100333 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100333
  have eq100469 : x = (M.op y x) ∨ y = (M.op (τ (σ x)) y) ∨ x = (k x y) := by grind
  clear eq100468
  have eq100470 : y = (k y x) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq100332
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq100332
    | exact resolve eq100332 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100332
  have eq100478 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq100469
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq100469
    | exact resolve eq100469 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100469
  have eq100479 : y = (k y x) ∨ x = (k x y) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq100470
       have r₂ := eq12 y x
       grind)
    | exact resolve eq100470 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100470
  have eq100484 : x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq100478
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq100478
       have r₂ := eq12 y x
       grind)
    | exact resolve eq100478 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100478
  have eq100489 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq406 y x
       have i₂ := eq100479
       grind)
    | exact superpose eq100479 eq406
    | (have j0 := eq406 y x
       grind)
    | exact resolve eq406 eq100479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100479
  have eq100491 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by grind
  clear eq100489
  have eq100497 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq100484
       grind)
    | exact superpose eq100484 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq100484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100484
  have eq100501 : y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq100497
  have eq100504 : ∀ X0 : G, x = (M.op (M.op (M.op y X0) X0) x) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq100501
       grind)
    | exact superpose eq100501 eq9
    | exact resolve eq9 eq100501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100519 : (M.op y x) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq228 x y
       have i₂ := eq100501
       grind)
    | exact superpose eq100501 eq228
    | exact resolve eq228 eq100501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100617 : (M.op y x) = (k y x) ∨ x = (M.op y x) := by grind
  clear eq100519
  have eq106072 : x = (k x (τ (σ y))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq77 x (σ y)
       have i₂ := eq100491
       grind)
    | exact superpose eq100491 eq77
    | exact resolve eq77 eq100491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100491
  have eq106216 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq106072
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq106072
    | exact resolve eq106072 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106072
  have eq106217 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by grind
  clear eq106216
  have eq106245 : ∀ X0 : G, y = (M.op (M.op (M.op (τ (σ x)) y) X0) y) ∨ y = (M.op (τ (σ x)) y) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq12218 y (σ x) x
       have i₂ := eq106217
       grind)
    | exact superpose eq106217 eq12218
    | exact resolve eq12218 eq106217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12218
  have eq106246 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) X0) (σ y)) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) (σ x) X0
       have i₂ := eq106217
       grind)
    | exact superpose eq106217 eq9
    | exact resolve eq9 eq106217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106217
  have eq106374 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) ∨ y = (M.op (τ (σ x)) y) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq106245 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq106245
    | exact resolve eq106245 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106245
  have eq106382 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op (M.op (M.op x y) X0) y) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq106374 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq106374
    | (have j0 := eq106374 X0
       grind)
    | exact resolve eq106374 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106374
  have eq106385 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) ∨ x = (k x y) := by
    intro X0
    first
    | (have j0 := eq106382 X0
       have j1 := eq12 x y
       grind)
    | (have r₁ := eq106382 X0
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq106382 X0
       have r₂ := eq12 (M.op (M.op x y) X0) y
       grind)
    | exact resolve eq106382 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106382
  have eq106663 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq230 x y y
       have i₂ := eq106385 y
       grind)
    | exact superpose eq106385 eq230
    | exact resolve eq230 eq106385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106385
  have eq106881 : (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq106663
       have r₂ := eq12 x y
       grind)
    | exact resolve eq106663 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106663
  have eq107919 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq230 (σ x) (σ y) (σ y)
       have i₂ := eq106246 (σ y)
       grind)
    | exact superpose eq106246 eq230
    | exact resolve eq230 eq106246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq106246
  have eq108137 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq107919
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq107919
    | exact resolve eq107919 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107919
  have eq108144 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq106881 eq108137
    | exact resolve eq108137 eq106881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106881 eq108137
  have eq108147 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have r₁ := eq108144
       have r₂ := eq16
       grind)
    | exact resolve eq108144 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108144
  have eq108151 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq77 x (σ y)
       have i₂ := eq108147
       grind)
    | exact superpose eq108147 eq77
    | exact resolve eq77 eq108147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108147
  have eq108318 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq108151
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq108151
    | exact resolve eq108151 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108151
  have eq108319 : x = (k x y) := by grind
  clear eq108318
  have eq108350 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq406 x y
       have i₂ := eq108319
       grind)
    | exact superpose eq108319 eq406
    | (have j0 := eq406 x y
       grind)
    | exact resolve eq406 eq108319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq108352 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq108350
  have eq108356 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq108352
       grind)
    | exact superpose eq108352 eq16
    | exact resolve eq16 eq108352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108511 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq108356
       have i₂ := eq100501
       grind)
    | exact superpose eq100501 eq108356
    | exact resolve eq108356 eq100501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100501
  have eq108512 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq108511
  have eq108514 : y = (k y (τ (σ x))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq77 y (σ x)
       have i₂ := eq108512
       grind)
    | exact superpose eq108512 eq77
    | exact resolve eq77 eq108512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq108512
  have eq108659 : y = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq108514
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq108514
    | exact resolve eq108514 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108514
  have eq108673 : y = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq108659
       have r₂ := eq12 y x
       grind)
    | exact resolve eq108659 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108659
  have eq108679 : y = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq100617
       have i₂ := eq108673
       grind)
    | exact superpose eq108673 eq100617
    | exact resolve eq100617 eq108673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100617 eq108673
  have eq108694 : x = (M.op (M.op y x) x) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq100504 x
       have i₂ := eq108679
       grind)
    | exact superpose eq108679 eq100504
    | exact resolve eq100504 eq108679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100504
  have eq108823 : x ≠ y ∨ x = (M.op y x) := by grind
  have eq108861 : x = (M.op y x) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq108679 eq108694
    | exact resolve eq108694 eq108679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108679 eq108694
  have eq108862 : x = (M.op y x) ∨ x = y := by grind
  clear eq108861
  have eq108871 : x = (M.op y x) := by
    first
    | (have r₁ := eq108862
       have r₂ := eq108823
       grind)
    | exact resolve eq108862 eq108823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108823 eq108862
  have eq108886 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq70 y x x
       have i₂ := eq108871
       grind)
    | exact superpose eq108871 eq70
    | exact resolve eq70 eq108871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq108893 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq228 y x
       have i₂ := eq108871
       grind)
    | exact superpose eq108871 eq228
    | exact resolve eq228 eq108871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq108995 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74601 y x
       have i₂ := eq108871
       grind)
    | exact superpose eq108871 eq74601
    | exact resolve eq74601 eq108871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74601 eq108871
  have eq109000 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq108995
       have i₂ := eq108319
       grind)
    | exact superpose eq108319 eq108995
    | exact resolve eq108995 eq108319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108995
  have eq109001 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108893
       have i₂ := eq108319
       grind)
    | exact superpose eq108319 eq108893
    | exact resolve eq108893 eq108319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108319 eq108893
  have eq109565 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108356
       have i₂ := eq109001
       grind)
    | exact superpose eq109001 eq108356
    | exact resolve eq108356 eq109001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109690 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq109565
  have eq109719 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq109690
  have eq112249 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq109719 eq108356
    | exact resolve eq108356 eq109719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108356 eq109719
  have eq117150 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq109000
       grind)
    | exact superpose eq109000 eq16
    | exact resolve eq16 eq109000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117321 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq117150
       have i₂ := eq109001
       grind)
    | exact superpose eq109001 eq117150
    | exact resolve eq117150 eq109001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109001 eq117150
  have eq117322 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq117321
  have eq117423 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9709 (σ x) (σ y)
       have i₂ := eq117322
       grind)
    | exact superpose eq117322 eq9709
    | exact resolve eq9709 eq117322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9709 eq117322
  have eq117472 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) := by grind
  clear eq117423
  have eq117489 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq117472
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq117472
    | exact resolve eq117472 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117472
  have eq117570 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq63 x y
       have i₂ := eq117489
       grind)
    | exact superpose eq117489 eq63
    | exact resolve eq63 eq117489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117489
  have eq117692 : x = (M.op x x) := by grind
  clear eq117570
  have eq117791 : y = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq108886 x
       have i₂ := eq117692
       grind)
    | exact superpose eq117692 eq108886
    | exact resolve eq108886 eq117692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108886
  have eq118015 : y = (M.op x y) := by
    first
    | (have i₁ := eq117791
       have i₂ := eq117692
       grind)
    | exact superpose eq117692 eq117791
    | exact resolve eq117791 eq117692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117692 eq117791
  have eq118066 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq118015
       grind)
    | exact superpose eq118015 eq16
    | exact resolve eq16 eq118015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118015
  have eq119368 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq118066
       have i₂ := eq109000
       grind)
    | exact superpose eq109000 eq118066
    | (have r₁ := eq118066
       have r₂ := eq109000
       grind)
    | exact resolve eq118066 eq109000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109000
  have eq119374 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq119368
  have eq119510 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq118066
       have i₂ := eq119374
       grind)
    | exact superpose eq119374 eq118066
    | exact resolve eq118066 eq119374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118066
  have eq119511 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq108352
       have i₂ := eq119374
       grind)
    | exact superpose eq119374 eq108352
    | exact resolve eq108352 eq119374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108352
  have eq119536 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq63 (σ x) (σ y)
       have i₂ := eq119374
       grind)
    | exact superpose eq119374 eq63
    | exact resolve eq63 eq119374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq119705 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq119511
       have r₂ := eq112249
       grind)
    | exact resolve eq119511 eq112249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112249 eq119511
  have eq120095 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12066 (σ y) (σ x) X0
       have i₂ := eq119705
       grind)
    | exact superpose eq119705 eq12066
    | exact resolve eq12066 eq119705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12066 eq119705
  have eq120159 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq120095 X0
       have i₂ := eq119374
       grind)
    | exact superpose eq119374 eq120095
    | exact resolve eq120095 eq119374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120095
  have eq123940 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq120159 (σ x)
       have i₂ := eq119536
       grind)
    | exact superpose eq119536 eq120159
    | exact resolve eq120159 eq119536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119536 eq120159
  have eq124206 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq123940
       have i₂ := eq119374
       grind)
    | exact superpose eq119374 eq123940
    | exact resolve eq123940 eq119374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119374 eq123940
  have eq124219 : False := by grind
  exact eq124219

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_y_pyx_pyy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
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
  have eq39 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) X0) X0) x) := by
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
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X1) X0 X0
       have i₂ := eq14 X0 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq76 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq77 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq77 y x
       grind)
    | exact superpose eq77 eq74
    | (have j1 := eq77 y x
       grind)
    | exact resolve eq74 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq108
    | exact resolve eq108 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq119 : x ≠ (M.op x y) ∨ x = (M.op y x) ∨ (k y x) = (M.op x x) := by
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
  have eq120 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq110 eq77
    | (have j0 := eq77 (σ y) (σ x)
       grind)
    | exact resolve eq77 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq124
    | exact resolve eq124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq125
       have r₂ := eq27
       grind)
    | exact resolve eq125 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq130 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq128
    | exact resolve eq128 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq132 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq130 eq27
    | exact resolve eq27 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq77 (σ X0) sF2
       grind)
    | exact superpose eq77 eq39
    | (have j1 := eq77 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq77
  have eq221 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq242 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) X0) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq130 eq51
    | exact resolve eq51 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq250 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq242 eq14
    | exact resolve eq14 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq277 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X1)
       have r₂ := eq54 X0 X1
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq283 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq277 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq497 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq130 eq120
    | (have r₁ := eq120
       have r₂ := eq130
       grind)
    | exact resolve eq120 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq130
  have eq498 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq497
  have eq1405 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq498 eq110
    | exact resolve eq110 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq1408 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq1405
  have eq1477 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1408 eq283
    | exact resolve eq283 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408
  have eq1479 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq1477
    | exact resolve eq1477 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477
  have eq1486 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1479 eq110
    | exact resolve eq110 eq1479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq1479
  have eq1489 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq1486
  have eq1493 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1489
       have r₂ := eq27
       grind)
    | exact resolve eq1489 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489
  have eq1497 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1493 eq250
    | exact resolve eq250 eq1493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq1493
  have eq1537 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1497
  have eq1540 : x = (M.op x y) := by
    first
    | (have r₁ := eq1537
       have r₂ := eq132
       grind)
    | exact resolve eq1537 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq1537
  have eq1542 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1540 eq20
    | exact resolve eq20 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1547 : x ≠ x ∨ x = (M.op y x) ∨ (k y x) = (M.op x x) := by
    first
    | exact superpose eq1540 eq119
    | (have r₁ := eq119
       have r₂ := eq1540
       grind)
    | exact resolve eq119 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq1551 : x = (M.op x x) := by
    first
    | exact superpose eq1540 eq221
    | exact resolve eq221 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq1556 : x = (M.op y x) ∨ (k y x) = (M.op x x) := by grind
  clear eq1547
  have eq1562 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1542
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1542
    | exact resolve eq1542 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542
  have eq1563 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1562 eq26
    | exact resolve eq26 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2552 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq1562 eq171
    | (have j0 := eq171 X0
       grind)
    | exact resolve eq171 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq2553 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq1562 eq2552
    | (have j0 := eq2552 X0
       grind)
    | exact resolve eq2552 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2552
  have eq2580 : (σ (k y x)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq2553 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2553
    | (have j0 := eq2553 y
       grind)
    | exact resolve eq2553 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2553
  have eq2598 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1563 eq2580
    | exact resolve eq2580 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2580
  have eq2615 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq2598
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq2598
    | exact resolve eq2598 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq2598
  have eq2626 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1562 eq2615
    | exact resolve eq2615 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2615
  have eq2635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1563 eq2626
    | exact resolve eq2626 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1563 eq2626
  have eq2642 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq2635
       have r₂ := eq27
       grind)
    | exact resolve eq2635 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2635
  have eq2658 : (k y (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2642 eq92
    | exact resolve eq92 eq2642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq2642
  have eq2660 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1540 eq2658
    | exact resolve eq2658 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2658
  have eq2909 : x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1556
       have i₂ := eq1551
       grind)
    | exact superpose eq1551 eq1556
    | exact resolve eq1556 eq1551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551 eq1556
  have eq2910 : x = (M.op y x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2909
       have i₂ := eq2660
       grind)
    | exact superpose eq2660 eq2909
    | exact resolve eq2909 eq2660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2909
  have eq2921 : (M.op x y) = (k y x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq283 y x
       have i₂ := eq2910
       grind)
    | exact superpose eq2910 eq283
    | exact resolve eq283 eq2910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283 eq2910
  have eq2923 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2921
       have i₂ := eq2660
       grind)
    | exact superpose eq2660 eq2921
    | exact resolve eq2921 eq2660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2660 eq2921
  have eq2927 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2923
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2923
    | exact resolve eq2923 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2923
  have eq2930 : x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1540 eq2927
    | exact resolve eq2927 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1540 eq2927
  have eq2931 : x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq2930
  have eq2935 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2931 eq15
    | exact resolve eq15 eq2931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2931
  have eq2946 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2935
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2935
    | exact resolve eq2935 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2935
  have eq2947 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1562 eq2946
    | exact resolve eq2946 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562 eq2946
  have eq2948 : False := by grind
  exact eq2948

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_y_pyx_y_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
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
  clear eq24
  have eq74 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq77 : x ≠ (M.op x y) ∨ x = (M.op y x) ∨ x = (k y x) := by
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
  have eq78 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq95 y x
       grind)
    | exact superpose eq95 eq74
    | (have j1 := eq95 y x
       grind)
    | exact resolve eq74 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq106
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq106
    | exact resolve eq106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq118
    | exact resolve eq118 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq120
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq120
    | exact resolve eq120 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq121 eq95
    | (have j0 := eq95 (σ y) (σ x)
       grind)
    | exact resolve eq95 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq124
    | exact resolve eq124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq125
       have r₂ := eq27
       grind)
    | exact resolve eq125 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq130 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq128
    | exact resolve eq128 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq132 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq130 eq27
    | exact resolve eq27 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq130 eq78
    | (have r₁ := eq78
       have r₂ := eq130
       grind)
    | exact resolve eq78 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq130
  have eq447 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq446
  have eq860 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq447 eq121
    | exact resolve eq121 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq864 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq860
  have eq869 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq864
       have r₂ := eq132
       grind)
    | exact resolve eq864 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq864
  have eq886 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq869 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq869
       grind)
    | exact resolve eq13 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq894 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq886
  have eq895 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq894
    | exact resolve eq894 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq901 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq895 eq121
    | exact resolve eq121 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq895
  have eq904 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq901
  have eq908 : x = (M.op x y) := by
    first
    | (have r₁ := eq904
       have r₂ := eq27
       grind)
    | exact resolve eq904 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq910 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq908 eq20
    | exact resolve eq20 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq915 : x ≠ x ∨ x = (M.op y x) ∨ x = (k y x) := by
    first
    | exact superpose eq908 eq77
    | (have r₁ := eq77
       have r₂ := eq908
       grind)
    | exact resolve eq77 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq922 : x = (k y x) ∨ x = (M.op y x) := by grind
  clear eq915
  have eq928 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq910
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq910
    | exact resolve eq910 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq929 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq928 eq26
    | exact resolve eq26 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1482 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq922
       grind)
    | exact superpose eq922 eq74
    | exact resolve eq74 eq922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq1489 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq928 eq1482
    | exact resolve eq1482 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482
  have eq1491 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1489
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1489
    | exact resolve eq1489 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489
  have eq1492 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq928 eq1491
    | exact resolve eq1491 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1491
  have eq1520 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1492 eq95
    | (have j0 := eq95 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq95 eq1492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492
  have eq1521 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq1520
  have eq1523 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq929 eq1521
    | exact resolve eq1521 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521
  have eq1526 : x = (M.op y x) := by
    first
    | (have r₁ := eq1523
       have r₂ := eq27
       grind)
    | exact resolve eq1523 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523
  have eq1531 : x ≠ x ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1526
       grind)
    | exact superpose eq1526 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1526
       grind)
    | exact resolve eq13 eq1526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526
  have eq1539 : (M.op x y) = (k y x) := by grind
  clear eq1531
  have eq1541 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1539
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1539
    | exact resolve eq1539 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1539
  have eq1543 : x = (k y x) := by
    first
    | exact superpose eq908 eq1541
    | exact resolve eq1541 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908 eq1541
  have eq1603 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq1543
       grind)
    | exact superpose eq1543 eq74
    | exact resolve eq74 eq1543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq1543
  have eq1610 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq928 eq1603
    | exact resolve eq1603 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603
  have eq1612 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1610
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1610
    | exact resolve eq1610 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1610
  have eq1613 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq928 eq1612
    | exact resolve eq1612 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928 eq1612
  have eq1616 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1613 eq95
    | (have j0 := eq95 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq95 eq1613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq1613
  have eq1617 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq1616
  have eq1619 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq929 eq1617
    | exact resolve eq1617 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929 eq1617
  have eq1622 : False := by grind
  exact eq1622

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pyx_pyy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X1)
       have r₂ := eq64 X0 X1
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq372 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq71
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq71 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq385 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq385 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq388 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq372 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq391 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq386 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq386 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq386 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq408 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq391 (σ X0)
       grind)
    | exact superpose eq391 eq15
    | exact resolve eq15 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq408 X0
       have i₂ := eq391 X0
       grind)
    | exact superpose eq391 eq408
    | exact resolve eq408 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq408
  have eq476 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq64 (σ X0) (σ X0)
       have i₂ := eq427 X0
       grind)
    | exact superpose eq427 eq64
    | exact resolve eq64 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq388 (σ X0) (σ X1)
       grind)
    | exact superpose eq388 eq15
    | (have j1 := eq388 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 X0) := by
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
  clear eq18 eq388
  have eq551 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq534 X0 X1
       have i₂ := eq427 X0
       grind)
    | exact superpose eq427 eq534
    | (have j0 := eq534 X0 X1
       grind)
    | exact resolve eq534 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427 eq534
  have eq1087 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq542 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq542
    | exact resolve eq542 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq1157 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1087 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1087
    | (have j0 := eq1087 X0 X1
       grind)
    | exact resolve eq1087 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq1642 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq551 x y
       grind)
    | exact superpose eq551 eq16
    | (have j1 := eq551 x y
       grind)
    | exact resolve eq16 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq1716 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1642
       have i₂ := eq1157 y x
       grind)
    | exact superpose eq1157 eq1642
    | (have j1 := eq1157 y x
       grind)
    | (have r₁ := eq1642
       have r₂ := eq1157 y x
       grind)
    | exact resolve eq1642 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157 eq1642
  have eq1717 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq1716
  have eq1724 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq476 x
       have i₂ := eq1717
       grind)
    | exact superpose eq1717 eq476
    | exact resolve eq476 eq1717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1737 : y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq64 x x
       have i₂ := eq1717
       grind)
    | exact superpose eq1717 eq64
    | exact resolve eq64 eq1717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717
  have eq1755 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1724
       grind)
    | exact superpose eq1724 eq16
    | exact resolve eq16 eq1724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724
  have eq1786 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1755
       have i₂ := eq1737
       grind)
    | exact superpose eq1737 eq1755
    | exact resolve eq1755 eq1737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1737 eq1755
  have eq1789 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq1786
  have eq1790 : (σ y) = (σ (M.op x x)) := by grind
  clear eq1789
  have eq1795 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq476 x
       have i₂ := eq1790
       grind)
    | exact superpose eq1790 eq476
    | exact resolve eq476 eq1790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq1796 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1790
       grind)
    | exact superpose eq1790 eq10
    | exact resolve eq10 eq1790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1790
  have eq1843 : y = (M.op x x) := by
    first
    | (have i₁ := eq1796
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1796
    | exact resolve eq1796 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796
  have eq1862 : y = (M.op x y) := by
    first
    | (have i₁ := eq64 x x
       have i₂ := eq1843
       grind)
    | exact superpose eq1843 eq64
    | exact resolve eq64 eq1843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq1843
  have eq1884 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1795
       grind)
    | exact superpose eq1795 eq16
    | exact resolve eq16 eq1795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795
  have eq1904 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1884
       have i₂ := eq1862
       grind)
    | exact superpose eq1862 eq1884
    | exact resolve eq1884 eq1862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1862 eq1884
  have eq1905 : False := by grind
  exact eq1905

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pyx_y_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
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
  have eq51 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) X0) X0) x) := by
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
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X1) X0 X0
       have i₂ := eq14 X0 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq93 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | (have r₁ := eq11 (M.op X0 (M.op X1 X1)) X1
       have r₂ := eq13 X0 (M.op X1 X1)
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq93
    | (have j0 := eq93 (σ X0) (σ X1)
       grind)
    | exact resolve eq93 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq93 x x
       grind)
    | exact superpose eq93 eq44
    | (have j1 := eq93 x x
       grind)
    | exact resolve eq44 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq93 y x
       grind)
    | exact superpose eq93 eq75
    | (have j1 := eq93 y x
       grind)
    | exact resolve eq75 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq104
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq104
    | exact resolve eq104 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq116
    | exact resolve eq116 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq125 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq136 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq125 eq16
    | exact resolve eq16 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq161 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq127 eq16
    | exact resolve eq16 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq202 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq227 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq13
    | (have j0 := eq13 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X1)
       have r₂ := eq55 X0 X1
       grind)
    | exact resolve eq13 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq227 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq579 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X1) (σ X0)
       have i₂ := eq97 X0 X1
       grind)
    | exact superpose eq97 eq55
    | (have j1 := eq97 X0 X1
       grind)
    | exact resolve eq55 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq97 X0 X1
       grind)
    | exact superpose eq97 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq97 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq97 X0 X0
       grind)
    | exact resolve eq13 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq586 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq580 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq580
    | (have j0 := eq580 X0 X1
       grind)
    | exact resolve eq580 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq673 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq117 eq93
    | (have j0 := eq93 (σ y) (σ x)
       grind)
    | exact resolve eq93 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq673
    | exact resolve eq673 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq677 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq674
       have r₂ := eq28
       grind)
    | exact resolve eq674 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq680 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq677 eq55
    | exact resolve eq55 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq684 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  have eq685 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq680
    | exact resolve eq680 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq687 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55 x x
       have i₂ := eq685
       grind)
    | exact superpose eq685 eq55
    | exact resolve eq55 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq692 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq687
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq687
    | exact resolve eq687 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq697 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq692 eq28
    | exact resolve eq28 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq1078 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq684 eq117
    | exact resolve eq117 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq1081 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1078
  have eq1097 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1081 eq232
    | exact resolve eq232 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq1081
  have eq1101 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq1097
    | exact resolve eq1097 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097
  have eq1155 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1101 eq117
    | exact resolve eq117 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq1158 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1155
  have eq1162 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1158
       have r₂ := eq28
       grind)
    | exact resolve eq1158 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158
  have eq1171 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq55 x x
       have i₂ := eq1162
       grind)
    | exact superpose eq1162 eq55
    | exact resolve eq55 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq1176 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1171
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1171
    | exact resolve eq1171 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171
  have eq1178 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1176 eq29
    | exact resolve eq29 eq1176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1181 : (k x x) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1176 eq50
    | exact resolve eq50 eq1176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1187 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1176 eq136
    | exact resolve eq136 eq1176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq1192 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1176 eq677
    | exact resolve eq677 eq1176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq1208 : (k (M.op x y) x) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq161 eq1187
    | exact resolve eq1187 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1212 : (k x x) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq161 eq1181
    | exact resolve eq1181 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161 eq1181
  have eq1215 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq1178
    | exact resolve eq1178 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq1628 : (k x x) = (k (M.op x y) x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1212 eq1208
    | exact resolve eq1208 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208 eq1212
  have eq1631 : (k x x) = (k (M.op x y) x) ∨ y = (M.op x y) := by grind
  clear eq1628
  have eq2102 : (k x x) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1631 eq93
    | (have j0 := eq93 (M.op x y) x
       grind)
    | exact resolve eq93 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1631
  have eq2103 : (M.op x y) = (k x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq202 eq2102
    | exact resolve eq2102 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq2102
  have eq24067 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq93 x x
       have i₂ := eq2103
       grind)
    | exact superpose eq2103 eq93
    | (have j0 := eq93 (M.op x y) x
       grind)
    | exact resolve eq93 eq2103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2103
  have eq24075 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq24067
  have eq26706 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq24075
  have eq26713 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq26706
       have r₂ := eq1215
       grind)
    | exact resolve eq26706 eq1215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215 eq26706
  have eq26855 : x ≠ x ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq26713
       grind)
    | exact superpose eq26713 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq26713
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq26713
       grind)
    | exact resolve eq13 eq26713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26713
  have eq26896 : x = (k x x) ∨ y = (M.op x y) := by grind
  clear eq26855
  have eq26922 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq586 x x
       have i₂ := eq26896
       grind)
    | exact superpose eq26896 eq586
    | (have j0 := eq586 x x
       grind)
    | exact resolve eq586 eq26896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586 eq26896
  have eq26926 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq26922
  have eq26927 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq26926
  have eq26945 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26927
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26927
    | exact resolve eq26927 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26927
  have eq27145 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1176 eq26945
    | exact resolve eq26945 eq1176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176 eq26945
  have eq27212 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq27145
  have eq27770 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27212 eq1192
    | exact resolve eq1192 eq27212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192 eq27212
  have eq27824 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq27770
  have eq27827 : y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq27824
       have r₂ := eq697
       grind)
    | exact resolve eq27824 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697 eq27824
  have eq29596 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq55 x x
       have i₂ := eq27827
       grind)
    | exact superpose eq27827 eq55
    | exact resolve eq55 eq27827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27827
  have eq29637 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29596
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29596
    | exact resolve eq29596 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq29596
  have eq29638 : y = (M.op x y) := by grind
  clear eq29637
  have eq29639 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq29638 eq21
    | exact resolve eq21 eq29638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq29766 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq29639
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq29639
    | exact resolve eq29639 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29639
  have eq29767 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq29766 eq27
    | exact resolve eq27 eq29766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29776 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29766 eq117
    | exact resolve eq117 eq29766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq32883 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29776 eq93
    | (have j0 := eq93 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq93 eq29776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq29776
  have eq32893 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29767 eq32883
    | exact resolve eq32883 eq29767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32883
  have eq32898 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq32893
       have r₂ := eq28
       grind)
    | exact resolve eq32893 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32893
  have eq33022 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32898 eq55
    | exact resolve eq55 eq32898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq32898
  have eq33062 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29767 eq33022
    | exact resolve eq33022 eq29767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33022
  have eq33064 : y = (M.op x x) := by
    first
    | (have r₁ := eq33062
       have r₂ := eq28
       grind)
    | exact resolve eq33062 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33062
  have eq33088 : x ≠ y ∨ y = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq33064
       grind)
    | exact superpose eq33064 eq13
    | exact resolve eq13 eq33064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33141 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq103
       have i₂ := eq33064
       grind)
    | exact superpose eq33064 eq103
    | exact resolve eq103 eq33064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq33142 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq33141
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33141
    | exact resolve eq33141 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33141
  have eq33143 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29766 eq33142
    | exact resolve eq33142 eq29766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33142
  have eq33144 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq33143
       have i₂ := eq33064
       grind)
    | exact superpose eq33064 eq33143
    | exact resolve eq33143 eq33064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33064 eq33143
  have eq33155 : (τ (σ (M.op x y))) = (k x x) ∨ x = y := by
    first
    | exact superpose eq33144 eq50
    | exact resolve eq50 eq33144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq33144
  have eq33181 : (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq31 eq33155
    | exact resolve eq33155 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq33155
  have eq33184 : y = (k x x) ∨ x = y := by
    first
    | exact superpose eq29638 eq33181
    | exact resolve eq33181 eq29638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29638 eq33181
  have eq33187 : y = (k x x) := by
    first
    | (have r₁ := eq33184
       have r₂ := eq33088
       grind)
    | exact resolve eq33184 eq33088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33088 eq33184
  have eq33194 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq33187
       grind)
    | exact superpose eq33187 eq44
    | exact resolve eq44 eq33187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq33214 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq579 x x
       have i₂ := eq33187
       grind)
    | exact superpose eq33187 eq579
    | (have j0 := eq579 x x
       grind)
    | exact resolve eq579 eq33187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579 eq33187
  have eq33229 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq33214
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33214
    | exact resolve eq33214 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33214
  have eq33241 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq33194
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33194
    | exact resolve eq33194 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq33194
  have eq33247 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq29766 eq33229
    | exact resolve eq33229 eq29766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33229
  have eq33258 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq29766 eq33241
    | exact resolve eq33241 eq29766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33241
  have eq33264 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq33247
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq33247
    | exact resolve eq33247 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33247
  have eq33275 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq29767 eq33264
    | exact resolve eq33264 eq29767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29767 eq33264
  have eq33281 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq33275
       have r₂ := eq28
       grind)
    | exact resolve eq33275 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33275
  have eq33284 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq33281
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq33281
    | exact resolve eq33281 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq33281
  have eq33356 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq33284 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq33284
       grind)
    | exact resolve eq13 eq33284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33397 : (σ x) = (k (σ x) (σ x)) := by grind
  clear eq33356
  have eq33409 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq33258 eq33397
    | exact resolve eq33397 eq33258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33258 eq33397
  have eq33419 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq33409 eq27
    | exact resolve eq27 eq33409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq33515 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq33409 eq33284
    | exact resolve eq33284 eq33409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33284 eq33409
  have eq33535 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq29766 eq33419
    | exact resolve eq33419 eq29766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29766 eq33419
  have eq34102 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33515 eq33535
    | exact resolve eq33535 eq33515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33515 eq33535
  have eq34103 : False := by grind
  exact eq34103

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pyx_pxx_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq22 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq12
    | (have j0 := eq12 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X1)
       have r₂ := eq22 X0 X1
       grind)
    | exact resolve eq12 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq33 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq52 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq87 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq89 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op (τ X1) X0) = X0 := by
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
  have eq109 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq52
    | exact resolve eq52 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq120 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq109 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq109
    | (have j0 := eq109 X0
       grind)
    | exact resolve eq109 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq109
  have eq121 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq120 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq120
    | (have j0 := eq120 X0
       grind)
    | exact resolve eq120 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq122 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq121 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq121 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq121 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq122 (σ X0)
       grind)
    | exact superpose eq122 eq15
    | exact resolve eq15 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq125 X0
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq125
    | exact resolve eq125 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq337 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq87 x y
       grind)
    | exact superpose eq87 eq16
    | (have j1 := eq87 x y
       grind)
    | exact resolve eq16 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq1312 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq89
    | exact resolve eq89 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq1367 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1312 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1312
    | (have j0 := eq1312 X0 X1
       grind)
    | exact resolve eq1312 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312
  have eq2248 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq337
       have i₂ := eq1367 y x
       grind)
    | exact superpose eq1367 eq337
    | (have j1 := eq1367 (σ x) (σ y)
       grind)
    | (have r₁ := eq337
       have r₂ := eq1367 y x
       grind)
    | (have r₁ := eq337
       have r₂ := eq1367 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq337
       have r₂ := eq1367 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq337 eq1367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2249 : x = y ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq2248
  have eq75479 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2249
       grind)
    | exact superpose eq2249 eq16
    | exact resolve eq16 eq2249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2249
  have eq75480 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq75479
       have r₂ := eq136 x
       grind)
    | exact resolve eq75479 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75479
  have eq75488 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq33 y x
       have i₂ := eq75480
       grind)
    | exact superpose eq75480 eq33
    | exact resolve eq33 eq75480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75480
  have eq76043 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq337
       have i₂ := eq75488
       grind)
    | exact superpose eq75488 eq337
    | exact resolve eq337 eq75488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337 eq75488
  have eq76081 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq76043
  have eq76082 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq76081
  have eq76085 : y = (τ (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq76082
       grind)
    | exact superpose eq76082 eq10
    | exact resolve eq10 eq76082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76082
  have eq76222 : x = y ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq76085
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq76085
    | exact resolve eq76085 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76085
  have eq76876 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq76222
       grind)
    | exact superpose eq76222 eq16
    | exact resolve eq16 eq76222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76222
  have eq76877 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq76876
       have r₂ := eq136 x
       grind)
    | exact resolve eq76876 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq76876
  have eq76910 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq33 (σ y) (σ x)
       have i₂ := eq76877
       grind)
    | exact superpose eq76877 eq33
    | exact resolve eq33 eq76877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76877
  have eq77037 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq76910
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq76910
    | exact resolve eq76910 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76910
  have eq77685 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77037
       grind)
    | exact superpose eq77037 eq16
    | exact resolve eq16 eq77037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77037
  have eq77852 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq77685
       have i₂ := eq1367 y x
       grind)
    | exact superpose eq1367 eq77685
    | (have j1 := eq1367 x y
       grind)
    | (have r₁ := eq77685
       have r₂ := eq1367 y x
       grind)
    | (have r₁ := eq77685
       have r₂ := eq1367 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq77685
       have r₂ := eq1367 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq77685 eq1367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367
  have eq77853 : x = y ∨ x = (M.op y x) := by grind
  clear eq77852
  have eq78664 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq77685
       have i₂ := eq77853
       grind)
    | exact superpose eq77853 eq77685
    | exact resolve eq77685 eq77853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77853
  have eq78665 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq78664
       have i₂ := eq122 x
       grind)
    | exact superpose eq122 eq78664
    | exact resolve eq78664 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq78664
  have eq78666 : x = (M.op y x) := by grind
  clear eq78665
  have eq78680 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq33 y x
       have i₂ := eq78666
       grind)
    | exact superpose eq78666 eq33
    | exact resolve eq33 eq78666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq78666
  have eq79692 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq77685
       have i₂ := eq78680
       grind)
    | exact superpose eq78680 eq77685
    | exact resolve eq77685 eq78680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77685 eq78680
  have eq79726 : False := by grind
  exact eq79726
