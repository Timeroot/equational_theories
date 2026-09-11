import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pxy_pyx_pxy_Equation2300 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq88 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq12 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq260 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq255 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq265 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq256 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq256 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq256 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq266 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq260 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq260 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq260 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq260 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq277 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq265 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq265
    | (have j0 := eq265 X0 X1
       grind)
    | exact resolve eq265 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq278 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq277 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq279 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq266 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq266
    | (have j0 := eq266 X0 X1
       grind)
    | exact resolve eq266 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq280 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq279 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq285 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq280 X0 X1
       have j1 := eq278 X0 X1
       grind)
    | (have r₁ := eq280 X0 X1
       have r₂ := eq278 X0 X1
       grind)
    | exact resolve eq280 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq280
  have eq286 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq285 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq285
    | exact resolve eq285 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq285 x y
       grind)
    | exact superpose eq285 eq16
    | exact resolve eq16 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq359 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq286 X0 (τ X1)
       grind)
    | exact superpose eq286 eq18
    | exact resolve eq18 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq286
  have eq384 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq359 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq359
    | exact resolve eq359 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq396 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq384 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq384
    | exact resolve eq384 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq428 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq297
       have i₂ := eq396 x y
       grind)
    | exact superpose eq396 eq297
    | exact resolve eq297 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297 eq396
  have eq429 : False := by grind
  exact eq429

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyx_pxy_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X0))) X0) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq271 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq271 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq271 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq271 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
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
  have eq426 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (M.op X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq429 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq434 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq856 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq429 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq3302 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) X0
       have i₂ := eq434 X0 X1
       grind)
    | exact superpose eq434 eq12
    | (have j1 := eq434 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) X0
       have r₂ := eq434 X0 X1
       grind)
    | exact resolve eq12 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3318 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (k y (τ (σ x))) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq434 (σ x) y
       grind)
    | exact superpose eq434 eq16
    | (have j1 := eq434 (σ x) y
       grind)
    | exact resolve eq16 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq3323 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3302 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3302
  have eq3327 : (σ (M.op x y)) ≠ (σ x) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq3318
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3318
    | exact resolve eq3318 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3318
  have eq9464 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (τ X0)) ∨ (M.op (τ X0) (M.op X1 (τ X0))) = (M.op (M.op X1 (τ X0)) (τ X0)) ∨ (k (σ (M.op X1 (τ X0))) X0) = (σ (M.op (τ X0) (M.op X1 (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1
       have i₂ := eq426 X0 (M.op X1 (τ X0))
       grind)
    | exact superpose eq426 eq9
    | (have j1 := eq426 X0 (M.op X1 (τ X0))
       grind)
    | exact resolve eq9 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9480 : ∀ X0 X1 : G, (τ X0) ≠ (M.op X1 (τ X0)) ∨ (M.op X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq426 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq9485 : ∀ X0 X1 : G, (M.op (τ X0) (M.op X1 (τ X0))) = (M.op (M.op X1 (τ X0)) (τ X0)) ∨ (k (σ (M.op X1 (τ X0))) X0) = (σ (M.op (τ X0) (M.op X1 (τ X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq9464 X0 X1
       have j1 := eq9480 X0 (M.op X1 (τ X0))
       grind)
    | (have r₁ := eq9464 X0 X1
       have r₂ := eq9480 X0 (M.op X1 (τ X0))
       grind)
    | exact resolve eq9464 eq9480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9464 eq9480
  have eq9939 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3323 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3323
    | exact resolve eq3323 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3323
  have eq10051 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9939 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq9939
    | (have j0 := eq9939 X0 X1
       grind)
    | exact resolve eq9939 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9939
  have eq10074 : ∀ X0 X1 : G, (M.op (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X0 X1))) ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10051 (τ X1) (τ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq10051
    | (have j0 := eq10051 (τ X0) (τ X1)
       grind)
    | exact resolve eq10051 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10051
  have eq15134 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq856 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq856
    | (have j0 := eq856 (τ X1) (τ X0)
       grind)
    | exact resolve eq856 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15198 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15134 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq15134
    | (have j0 := eq15134 X0 X1
       grind)
    | exact resolve eq15134 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15134
  have eq15225 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15198 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq15198
    | (have j0 := eq15198 X0 X1
       grind)
    | exact resolve eq15198 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15198
  have eq15251 : ∀ X0 X1 : G, (M.op X0 (σ (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15225 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15225
    | (have j0 := eq15225 X0 X1
       grind)
    | exact resolve eq15225 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15225
  have eq15273 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15251 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15251
    | (have j0 := eq15251 X0 X1
       grind)
    | exact resolve eq15251 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15251
  have eq15290 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15273 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15273
    | (have j0 := eq15273 X0 X1
       grind)
    | exact resolve eq15273 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15273
  have eq15303 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15290 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15290
    | (have j0 := eq15290 X0 X1
       grind)
    | exact resolve eq15290 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15290
  have eq248487 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) X0) ∨ (σ (M.op X0 (M.op X1 X0))) = (k (σ (M.op X1 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9485 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9485
    | exact resolve eq9485 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9485
  have eq248638 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) X0) ∨ (σ (k (M.op X1 X0) X0)) = (σ (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq248487 X0 X1
       have i₂ := eq15 (M.op X1 X0) X0
       grind)
    | exact superpose eq15 eq248487
    | (have j0 := eq248487 X0 X1
       grind)
    | exact resolve eq248487 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248487
  have eq248777 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X0 (M.op X1 X0)) = X0 ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) X0) ∨ (σ (k (M.op X1 X0) X0)) = (σ (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X1 X0) X0
       have i₂ := eq248638 X0 X1
       grind)
    | exact superpose eq248638 eq13
    | (have j0 := eq13 (M.op X1 X0) X0
       have j1 := eq248638 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X1 X0) X0
       have r₂ := eq248638 X0 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X0)
       have r₂ := eq248638 X0 X1
       grind)
    | exact resolve eq13 eq248638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248638
  have eq248821 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) X0) ∨ (σ (k (M.op X1 X0) X0)) = (σ (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq248777 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248777
  have eq248847 : ∀ X0 X1 : G, (σ (k (M.op X1 X0) X0)) = (σ (M.op X0 (M.op X1 X0))) ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have j0 := eq248821 X0 X1
       have j1 := eq12 (M.op X1 X0) X0
       grind)
    | (have r₁ := eq248821 X1 X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq248821 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248821
  have eq249168 : ∀ X0 X1 : G, (k (M.op X1 X0) X0) = (τ (σ (M.op X0 (M.op X1 X0)))) ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (M.op X1 X0) X0)
       have i₂ := eq248847 X0 X1
       grind)
    | exact superpose eq248847 eq10
    | (have j1 := eq248847 X0 X1
       grind)
    | exact resolve eq10 eq248847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248847
  have eq249399 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) X0) ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq249168 X0 X1
       have i₂ := eq10 (M.op X0 (M.op X1 X0))
       grind)
    | exact superpose eq10 eq249168
    | (have j0 := eq249168 X0 X1
       grind)
    | exact resolve eq249168 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249168
  have eq249400 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have j0 := eq249399 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249399
  have eq668210 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) (τ X0)
       have i₂ := eq10074 X0 X1
       grind)
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq10074 X0 X1
       grind)
    | exact superpose eq10074 eq13
    | (have j0 := eq13 (τ X1) (τ X0)
       have j1 := eq10074 X1 X0
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq10074 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) (τ X0)
       have r₂ := eq10074 X0 X1
       grind)
    | exact resolve eq13 eq10074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10074
  have eq668254 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq668210 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668210
  have eq668274 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq668254 X0 X1
       have j1 := eq12 (τ X1) (τ X0)
       grind)
    | (have r₁ := eq668254 X0 X1
       have r₂ := eq12 (τ X1) (τ X0)
       grind)
    | exact resolve eq668254 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668254
  have eq668337 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq668274 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq668274
    | (have j0 := eq668274 X0 X1
       grind)
    | exact resolve eq668274 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq668274
  have eq668393 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (M.op X0 (τ X1)) ∨ (τ (M.op X0 (τ X1))) = (τ (τ (k X1 (σ X0)))) ∨ (τ (k X1 (σ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq668337 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq668337
    | exact resolve eq668337 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668337
  have eq669047 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op X0 (τ X1)) ∨ (τ (M.op X0 (τ X1))) = (τ (τ (k X1 (σ X0)))) ∨ (τ (k X1 (σ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq668393 X0 X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq668393
    | (have j0 := eq668393 X0 X1
       grind)
    | exact resolve eq668393 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668393
  have eq669177 : ∀ X0 X1 : G, (τ (k (τ X1) X0)) = (τ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = (M.op X0 (τ X1)) ∨ (τ (k X1 (σ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq669047 X0 X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq669047
    | (have j0 := eq669047 X0 X1
       grind)
    | exact resolve eq669047 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669047
  have eq669258 : ∀ X0 X1 : G, (τ (k (τ X1) X0)) = (τ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 ∨ (k (τ X1) X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq669177 X0 X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq669177
    | (have j0 := eq669177 X0 X1
       grind)
    | exact resolve eq669177 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669177
  have eq669583 : ∀ X0 X1 : G, (k (τ X1) X0) = (σ (τ (M.op X0 (τ X1)))) ∨ (k (τ X1) X0) = X0 ∨ (k (τ X1) X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k (τ X1) X0)
       have i₂ := eq669258 X0 X1
       grind)
    | exact superpose eq669258 eq11
    | (have j1 := eq669258 X0 X1
       grind)
    | exact resolve eq11 eq669258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669258
  have eq671503 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op X0 (τ X1)) ∨ (k (τ X1) X0) = X0 ∨ (k (τ X1) X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq669583 X0 X1
       have i₂ := eq11 (M.op X0 (τ X1))
       grind)
    | exact superpose eq11 eq669583
    | (have j0 := eq669583 X0 X1
       grind)
    | exact resolve eq669583 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669583
  have eq671504 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op X0 (τ X1)) ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq671503 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671503
  have eq671556 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq671504 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq671504
    | exact resolve eq671504 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671719 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq671504 X0 X1
       grind)
    | exact superpose eq671504 eq17
    | (have j1 := eq671504 X0 X1
       grind)
    | exact resolve eq17 eq671504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq671504
  have eq674181 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq671556 (σ X1) X0
       grind)
    | exact superpose eq671556 eq28
    | (have j1 := eq671556 (σ X1) X0
       grind)
    | exact resolve eq28 eq671556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq671556
  have eq676034 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq671719 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq671719
    | exact resolve eq671719 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671719
  have eq676535 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq676034 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq676034
    | (have j0 := eq676034 X0 X1
       grind)
    | exact resolve eq676034 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676034
  have eq678566 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq674181 (σ X0) X1
       grind)
    | exact superpose eq674181 eq15
    | (have j1 := eq674181 (σ X0) X1
       grind)
    | exact resolve eq15 eq674181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq678696 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq674181 (σ X0) X1
       grind)
    | exact superpose eq674181 eq22
    | (have j1 := eq674181 (σ X0) X1
       grind)
    | exact resolve eq22 eq674181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq674181
  have eq679528 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq678696 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq678696
    | (have j0 := eq678696 X0 X1
       grind)
    | exact resolve eq678696 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678696
  have eq679563 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq678566 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq678566
    | (have j0 := eq678566 X0 X1
       grind)
    | exact resolve eq678566 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678566
  have eq679969 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq679528 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq679528
    | (have j0 := eq679528 X0 X1
       grind)
    | exact resolve eq679528 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679528
  have eq680039 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq679969 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq679969
    | (have j0 := eq679969 X0 X1
       grind)
    | exact resolve eq679969 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679969
  have eq682903 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq680039 X1 X0
       grind)
    | exact superpose eq680039 eq11
    | (have j1 := eq680039 X1 X0
       grind)
    | exact resolve eq11 eq680039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680039
  have eq684655 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq682903 y x
       grind)
    | exact superpose eq682903 eq16
    | (have j1 := eq682903 y x
       grind)
    | exact resolve eq16 eq682903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682903
  have eq685063 : x = (k y x) := by
    first
    | (have j1 := eq676535 y x
       grind)
    | (have r₁ := eq684655
       have r₂ := eq676535 y x
       grind)
    | exact resolve eq684655 eq676535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676535 eq684655
  have eq685425 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq856 x y
       have i₂ := eq685063
       grind)
    | exact superpose eq685063 eq856
    | (have j0 := eq856 y x
       grind)
    | exact resolve eq856 eq685063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq685443 : x ≠ x ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15303 y x
       have i₂ := eq685063
       grind)
    | exact superpose eq685063 eq15303
    | (have j0 := eq15303 y x
       grind)
    | (have r₁ := eq15303 y x
       have r₂ := eq685063
       grind)
    | exact resolve eq15303 eq685063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15303
  have eq685512 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq685443
  have eq685514 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq685425
  have eq685533 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq685512
       grind)
    | exact superpose eq685512 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq685512
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq685512
       grind)
    | exact resolve eq13 eq685512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685512
  have eq685578 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq685533
  have eq685579 : x = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq685578
  have eq685581 : (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq685579
       have r₂ := eq12 y x
       grind)
    | exact resolve eq685579 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685579
  have eq685593 : x = (M.op x y) := by
    first
    | (have i₁ := eq685581
       have i₂ := eq685063
       grind)
    | exact superpose eq685063 eq685581
    | exact resolve eq685581 eq685063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685581
  have eq685595 : (σ x) ≠ (σ x) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq3327
       have i₂ := eq685593
       grind)
    | exact superpose eq685593 eq3327
    | exact resolve eq3327 eq685593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3327
  have eq685596 : y = (M.op (M.op x (M.op y x)) y) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq685593
       grind)
    | exact superpose eq685593 eq9
    | exact resolve eq9 eq685593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq685671 : (M.op y x) = (k x y) := by
    first
    | (have i₁ := eq249400 y x
       have i₂ := eq685593
       grind)
    | exact superpose eq685593 eq249400
    | exact resolve eq249400 eq685593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249400
  have eq685679 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq685595
  have eq685702 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq685679
       have i₂ := eq685063
       grind)
    | exact superpose eq685063 eq685679
    | exact resolve eq685679 eq685063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685679
  have eq717454 : (σ y) = (σ (M.op y x)) ∨ (M.op y x) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq679563 y x
       have i₂ := eq685671
       grind)
    | exact superpose eq685671 eq679563
    | exact resolve eq679563 eq685671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679563 eq685671
  have eq729700 : (τ (σ y)) = (M.op y x) ∨ (M.op y x) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq10 (M.op y x)
       have i₂ := eq717454
       grind)
    | exact superpose eq717454 eq10
    | exact resolve eq10 eq717454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717454
  have eq729987 : y = (M.op y x) ∨ (M.op y x) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq729700
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq729700
    | exact resolve eq729700 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729700
  have eq729991 : y = (M.op (M.op x y) y) ∨ (M.op y x) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq685596
       have i₂ := eq729987
       grind)
    | exact superpose eq729987 eq685596
    | exact resolve eq685596 eq729987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685596 eq729987
  have eq730166 : y = (M.op x y) ∨ (M.op y x) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq729991
       have i₂ := eq685593
       grind)
    | exact superpose eq685593 eq729991
    | exact resolve eq729991 eq685593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729991
  have eq730206 : x = y ∨ (M.op y x) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq730166
       have i₂ := eq685593
       grind)
    | exact superpose eq685593 eq730166
    | exact resolve eq730166 eq685593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730166
  have eq730231 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op y x) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq730206
       grind)
    | exact superpose eq730206 eq16
    | exact resolve eq16 eq730206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730206
  have eq730252 : (M.op y x) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have r₁ := eq730231
       have r₂ := eq302 x
       grind)
    | exact resolve eq730231 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302 eq730231
  have eq730292 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq11 (M.op (σ y) (σ x))
       have i₂ := eq730252
       grind)
    | exact superpose eq730252 eq11
    | exact resolve eq11 eq730252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730252
  have eq878643 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq685514
       grind)
    | exact superpose eq685514 eq16
    | exact resolve eq16 eq685514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685514
  have eq878878 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq878643
       have i₂ := eq685593
       grind)
    | exact superpose eq685593 eq878643
    | exact resolve eq878643 eq685593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878643
  have eq878879 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq878878
  have eq878980 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq878879
       have i₂ := eq730292
       grind)
    | exact superpose eq730292 eq878879
    | exact resolve eq878879 eq730292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730292 eq878879
  have eq879162 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq878980
       grind)
    | exact superpose eq878980 eq16
    | exact resolve eq16 eq878980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq879360 : (σ x) ≠ (σ (M.op y x)) := by
    first
    | (have i₁ := eq879162
       have i₂ := eq685593
       grind)
    | exact superpose eq685593 eq879162
    | exact resolve eq879162 eq685593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685593 eq879162
  have eq935088 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq685702
       grind)
    | exact superpose eq685702 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq685702
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq685702
       grind)
    | exact resolve eq13 eq685702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685702
  have eq935140 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq935088
  have eq935193 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq935140
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq935140 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935140
  have eq935291 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq935193
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq935193
    | exact resolve eq935193 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935193
  have eq935348 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq935291
       have i₂ := eq685063
       grind)
    | exact superpose eq685063 eq935291
    | exact resolve eq935291 eq685063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685063 eq935291
  have eq935388 : (σ x) = (σ (M.op y x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq935348
       have i₂ := eq878980
       grind)
    | exact superpose eq878980 eq935348
    | exact resolve eq935348 eq878980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935348
  have eq935423 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq935388
       have r₂ := eq879360
       grind)
    | exact resolve eq935388 eq879360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935388
  have eq935445 : x = (τ (σ (M.op y x))) := by
    first
    | (have i₁ := eq935423
       have i₂ := eq878980
       grind)
    | exact superpose eq878980 eq935423
    | exact resolve eq935423 eq878980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878980 eq935423
  have eq935458 : x = (M.op y x) := by
    first
    | (have i₁ := eq935445
       have i₂ := eq10 (M.op y x)
       grind)
    | exact superpose eq10 eq935445
    | exact resolve eq935445 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935445
  have eq935495 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq879360
       have i₂ := eq935458
       grind)
    | exact superpose eq935458 eq879360
    | exact resolve eq879360 eq935458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879360 eq935458
  have eq935603 : False := by grind
  exact eq935603

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation2300 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  clear eq28
  have eq466 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3121 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq466 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq466
    | exact resolve eq466 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq3165 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3121 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3121
    | (have j0 := eq3121 X0 X1
       grind)
    | exact resolve eq3121 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3121
  have eq3169 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X0))) ∨ (M.op (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3165 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq3165
    | (have j0 := eq3165 (τ X0) (τ X1)
       grind)
    | exact resolve eq3165 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3165
  have eq3262 : ∀ X0 X1 : G, (M.op (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3169 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3169
    | (have j0 := eq3169 X0 X1
       grind)
    | exact resolve eq3169 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3169
  have eq19673 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) (τ X0)
       have i₂ := eq3262 X0 X1
       grind)
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq3262 X0 X1
       grind)
    | exact superpose eq3262 eq13
    | (have j0 := eq13 (τ X0) (τ X1)
       have j1 := eq3262 X1 X0
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq3262 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) (τ X0)
       have r₂ := eq3262 X0 X1
       grind)
    | exact resolve eq13 eq3262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3262
  have eq19679 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq19673 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19673
  have eq19680 : ∀ X0 X1 : G, (τ X0) = (τ X1) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq19679 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19679
  have eq19700 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19680 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq19680
    | (have j0 := eq19680 X0 X1
       grind)
    | exact resolve eq19680 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq19680
  have eq19741 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19700 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19700
    | exact resolve eq19700 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19700
  have eq19819 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19741 X0 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq19741
    | (have j0 := eq19741 X0 X1
       grind)
    | exact resolve eq19741 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19741
  have eq19870 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X1) X0)
       have i₂ := eq19819 X0 X1
       grind)
    | exact superpose eq19819 eq10
    | (have j1 := eq19819 X0 X1
       grind)
    | exact resolve eq10 eq19819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19819
  have eq19982 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19870 X0 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq19870
    | (have j0 := eq19870 X0 X1
       grind)
    | exact resolve eq19870 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq19870
  have eq19983 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq19982 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19982
  have eq20004 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19983 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19983
    | exact resolve eq19983 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20043 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq19983 X1 X0
       grind)
    | exact superpose eq19983 eq19
    | (have j1 := eq19983 X1 X0
       grind)
    | exact resolve eq19 eq19983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq19983
  have eq20370 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq20004 (σ X0) (σ X1)
       grind)
    | exact superpose eq20004 eq15
    | (have j1 := eq20004 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq20004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20004
  have eq20504 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20043 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20043
    | exact resolve eq20043 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20043
  have eq20662 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20504 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq20504
    | (have j0 := eq20504 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq20504 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20504
  have eq22267 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20370 x y
       grind)
    | exact superpose eq20370 eq16
    | (have j1 := eq20370 x y
       grind)
    | exact resolve eq16 eq20370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20370
  have eq22336 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq22267
       have i₂ := eq20662 x y
       grind)
    | exact superpose eq20662 eq22267
    | (have j1 := eq20662 (σ x) (σ y)
       grind)
    | (have r₁ := eq22267
       have r₂ := eq20662 x y
       grind)
    | (have r₁ := eq22267
       have r₂ := eq20662 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq22267
       have r₂ := eq20662 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq22267 eq20662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20662 eq22267
  have eq22339 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq22336
  have eq22342 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22339
       grind)
    | exact superpose eq22339 eq16
    | exact resolve eq16 eq22339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22339
  have eq22343 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq22342
       have r₂ := eq22 x
       grind)
    | exact resolve eq22342 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22342
  have eq22344 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22343
       grind)
    | exact superpose eq22343 eq16
    | exact resolve eq16 eq22343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22345 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq22343
       grind)
    | exact superpose eq22343 eq10
    | exact resolve eq10 eq22343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22343
  have eq22518 : x = y := by
    first
    | (have i₁ := eq22345
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22345
    | exact resolve eq22345 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22345
  have eq22519 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq22344
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq22344
    | exact resolve eq22344 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq22344
  have eq22520 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq22519
       have i₂ := eq22518
       grind)
    | exact superpose eq22518 eq22519
    | exact resolve eq22519 eq22518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22518 eq22519
  have eq22521 : False := by grind
  exact eq22521

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation2300 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2300 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq466 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3123 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq466 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq466
    | exact resolve eq466 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq3183 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3123 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3123
    | (have j0 := eq3123 X0 X1
       grind)
    | exact resolve eq3123 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3123
  have eq3196 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3183 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq3183
    | (have j0 := eq3183 (τ X1) (τ X0)
       grind)
    | exact resolve eq3183 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3183
  have eq3289 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3196 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3196
    | (have j0 := eq3196 X0 X1
       grind)
    | exact resolve eq3196 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3196
  have eq19673 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) (τ X0)
       have i₂ := eq3289 X0 X1
       grind)
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq3289 X0 X1
       grind)
    | exact superpose eq3289 eq13
    | (have j0 := eq13 (τ X0) (τ X1)
       have j1 := eq3289 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) (τ X0)
       have r₂ := eq3289 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq3289 X0 X1
       grind)
    | exact resolve eq13 eq3289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3289
  have eq19682 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq19673 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19673
  have eq19683 : ∀ X0 X1 : G, (τ X0) = (τ X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq19682 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19682
  have eq19702 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19683 X0 X1
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq19683
    | (have j0 := eq19683 X0 X1
       grind)
    | exact resolve eq19683 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq19683
  have eq26314 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (M.op (τ X1) X0) ∨ (τ X1) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19702 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19702
    | exact resolve eq19702 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19702
  have eq26408 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq26314 X0 X1
       have i₂ := eq28 X1 X0
       grind)
    | exact superpose eq28 eq26314
    | (have j0 := eq26314 X0 X1
       grind)
    | exact resolve eq26314 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26314
  have eq26469 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) X1)
       have i₂ := eq26408 X1 X0
       grind)
    | exact superpose eq26408 eq10
    | (have j1 := eq26408 X1 X0
       grind)
    | exact resolve eq10 eq26408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26408
  have eq26586 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26469 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq26469
    | (have j0 := eq26469 X0 X1
       grind)
    | exact resolve eq26469 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq26469
  have eq26587 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq26586 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26586
  have eq26613 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26587 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26587
    | exact resolve eq26587 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26660 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq26587 X0 X1
       grind)
    | exact superpose eq26587 eq18
    | (have j1 := eq26587 X0 X1
       grind)
    | exact resolve eq18 eq26587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq26587
  have eq27010 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq26613 (σ X0) (σ X1)
       grind)
    | exact superpose eq26613 eq15
    | (have j1 := eq26613 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq26613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26613
  have eq27151 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26660 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26660
    | exact resolve eq26660 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26660
  have eq27322 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27151 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq27151
    | (have j0 := eq27151 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq27151 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27151
  have eq28939 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27010 x y
       grind)
    | exact superpose eq27010 eq16
    | (have j1 := eq27010 x y
       grind)
    | exact resolve eq16 eq27010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27010
  have eq29015 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq28939
       have i₂ := eq27322 x y
       grind)
    | exact superpose eq27322 eq28939
    | (have j1 := eq27322 (σ x) (σ y)
       grind)
    | (have r₁ := eq28939
       have r₂ := eq27322 x y
       grind)
    | (have r₁ := eq28939
       have r₂ := eq27322 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq28939
       have r₂ := eq27322 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq28939 eq27322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27322 eq28939
  have eq29020 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq29015
  have eq29024 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29020
       grind)
    | exact superpose eq29020 eq16
    | exact resolve eq16 eq29020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29020
  have eq29025 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq29024
       have r₂ := eq22 x
       grind)
    | exact resolve eq29024 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29024
  have eq29026 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29025
       grind)
    | exact superpose eq29025 eq16
    | exact resolve eq16 eq29025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29027 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq29025
       grind)
    | exact superpose eq29025 eq10
    | exact resolve eq10 eq29025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29025
  have eq29202 : x = y := by
    first
    | (have i₁ := eq29027
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq29027
    | exact resolve eq29027 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29027
  have eq29203 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq29026
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq29026
    | exact resolve eq29026 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq29026
  have eq29204 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq29203
       have i₂ := eq29202
       grind)
    | exact superpose eq29202 eq29203
    | exact resolve eq29203 eq29202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29202 eq29203
  have eq29205 : False := by grind
  exact eq29205

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation2300 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  clear eq28
  have eq468 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq37
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq37 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq471 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq3214 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq471 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq471
    | exact resolve eq471 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq3273 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3214 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3214
    | (have j0 := eq3214 X0 X1
       grind)
    | exact resolve eq3214 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3214
  have eq3535 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (σ X1) = X0 ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq468 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq468 X0 X1
       grind)
    | exact superpose eq468 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq468 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq468 (σ X1) X1
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq468 X0 X1
       grind)
    | exact resolve eq13 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3538 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (k y (τ (σ x))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq468 (σ x) y
       grind)
    | exact superpose eq468 eq16
    | (have j1 := eq468 (σ x) y
       grind)
    | (have r₁ := eq16
       have r₂ := eq468 (M.op (σ x) (σ y)) (M.op x y)
       grind)
    | exact resolve eq16 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq3546 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (σ X1) = X0 ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3535 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3535
  have eq3547 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3546 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3546
  have eq3553 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y (τ (σ x))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3538
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq3538
    | exact resolve eq3538 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3538
  have eq3568 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3553
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3553
    | exact resolve eq3553 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3553
  have eq3780 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3547 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3547
    | exact resolve eq3547 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3547
  have eq3885 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3780 X0 X1
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq3780
    | (have j0 := eq3780 X0 X1
       grind)
    | exact resolve eq3780 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq3780
  have eq3968 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq3885 X1 X0
       grind)
    | exact superpose eq3885 eq11
    | (have j1 := eq3885 X1 X0
       grind)
    | exact resolve eq11 eq3885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3885
  have eq4087 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3968 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq3968
    | (have j0 := eq3968 X0 X1
       grind)
    | exact resolve eq3968 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3968
  have eq4107 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4087 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4087
    | (have j0 := eq4087 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq4087 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4156 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq4087 X0 (τ X1)
       grind)
    | exact superpose eq4087 eq18
    | (have j1 := eq4087 X0 (τ X1)
       grind)
    | exact resolve eq18 eq4087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4087
  have eq4265 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4107 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq4107
    | (have j0 := eq4107 X0 X1
       grind)
    | exact resolve eq4107 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4107
  have eq4378 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4156 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4156
    | exact resolve eq4156 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4156
  have eq4446 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4378 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4378
    | (have j0 := eq4378 X0 X1
       grind)
    | exact resolve eq4378 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4378
  have eq11792 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4265 y x
       grind)
    | exact superpose eq4265 eq16
    | (have j1 := eq4265 y x
       grind)
    | exact resolve eq16 eq4265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4265
  have eq11876 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq11792
       have i₂ := eq3273 y x
       grind)
    | exact superpose eq3273 eq11792
    | (have j1 := eq3273 y x
       grind)
    | (have r₁ := eq11792
       have r₂ := eq3273 y x
       grind)
    | (have r₁ := eq11792
       have r₂ := eq3273 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq11792
       have r₂ := eq3273 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq11792 eq3273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11792
  have eq11877 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq11876
  have eq12003 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11877
       grind)
    | exact superpose eq11877 eq16
    | exact resolve eq16 eq11877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11877
  have eq12004 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq12003
       have r₂ := eq22 x
       grind)
    | exact resolve eq12003 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12003
  have eq12005 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3568
       have i₂ := eq12004
       grind)
    | exact superpose eq12004 eq3568
    | (have r₁ := eq3568
       have r₂ := eq12004
       grind)
    | exact resolve eq3568 eq12004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12004
  have eq12012 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq12005
  have eq12013 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq12012
  have eq12014 : (σ x) = (σ y) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq12013
       have r₂ := eq3568
       grind)
    | exact resolve eq12013 eq3568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3568 eq12013
  have eq12016 : y = (τ (σ x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq12014
       grind)
    | exact superpose eq12014 eq10
    | exact resolve eq10 eq12014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12014
  have eq12079 : x = y ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq12016
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12016
    | exact resolve eq12016 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12016
  have eq12081 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12079
       grind)
    | exact superpose eq12079 eq16
    | exact resolve eq16 eq12079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12079
  have eq12082 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq12081
       have r₂ := eq22 x
       grind)
    | exact resolve eq12081 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12081
  have eq12096 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq12082
       grind)
    | exact superpose eq12082 eq11
    | exact resolve eq11 eq12082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12082
  have eq12186 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12096
       grind)
    | exact superpose eq12096 eq16
    | exact resolve eq16 eq12096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12096
  have eq12224 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k y x) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq12186
       have i₂ := eq4446 y x
       grind)
    | exact superpose eq4446 eq12186
    | (have j1 := eq4446 y x
       grind)
    | (have r₁ := eq12186
       have r₂ := eq4446 y x
       grind)
    | (have r₁ := eq12186
       have r₂ := eq4446 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq12186
       have r₂ := eq4446 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq12186 eq4446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4446
  have eq12225 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq12186
       have i₂ := eq3273 y x
       grind)
    | exact superpose eq3273 eq12186
    | (have j1 := eq3273 y x
       grind)
    | (have r₁ := eq12186
       have r₂ := eq3273 y x
       grind)
    | (have r₁ := eq12186
       have r₂ := eq3273 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq12186
       have r₂ := eq3273 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq12186 eq3273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3273
  have eq12226 : (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq12225
  have eq12227 : x = y ∨ (k y x) = (M.op x x) := by grind
  clear eq12224
  have eq12242 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq12186
       have i₂ := eq12227
       grind)
    | exact superpose eq12227 eq12186
    | exact resolve eq12186 eq12227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12227
  have eq12243 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq12242
  have eq12244 : (k y x) = (M.op x x) := by grind
  clear eq12243
  have eq12253 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12186
       have i₂ := eq12244
       grind)
    | exact superpose eq12244 eq12186
    | exact resolve eq12186 eq12244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12186 eq12244
  have eq12285 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq12253
       have i₂ := eq12226
       grind)
    | exact superpose eq12226 eq12253
    | exact resolve eq12253 eq12226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12226
  have eq12290 : x = y := by grind
  clear eq12285
  have eq12301 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12253
       have i₂ := eq12290
       grind)
    | exact superpose eq12290 eq12253
    | exact resolve eq12253 eq12290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12253 eq12290
  have eq12302 : False := by grind
  exact eq12302

/-- `Equation2340`: `x = (y ◇ (y ◇ (y ◇ y))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pxx_pyy_pyx_Equation2340 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2340 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2340.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 (M.op X1 X1))) X0) = X0 := by
    intro X0 X1
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
  have eq76 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq76
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq76
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq89
    | exact resolve eq89 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq95
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96
    | exact resolve eq96 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq109 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) := by
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
  have eq110 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq112 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq112 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq112 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq115 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq113 (σ X0)
       grind)
    | exact superpose eq113 eq10
    | exact resolve eq10 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq113 x
       grind)
    | exact superpose eq113 eq43
    | exact resolve eq43 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq118 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq113 sF2
       grind)
    | exact superpose eq113 eq49
    | exact resolve eq49 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq119 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq118
       have i₂ := eq113 x
       grind)
    | exact superpose eq113 eq118
    | exact resolve eq118 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq121 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq113 sF2
       grind)
    | exact superpose eq113 eq116
    | exact resolve eq116 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq122 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq115 X0
       have i₂ := eq113 X0
       grind)
    | exact superpose eq113 eq115
    | exact resolve eq115 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq115
  have eq595 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 X1
       have i₂ := eq122 X1
       grind)
    | exact superpose eq122 eq79
    | (have j0 := eq79 X0 X1
       grind)
    | exact resolve eq79 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq596 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq595 X0 X1
       have i₂ := eq122 X1
       grind)
    | exact superpose eq122 eq595
    | (have j0 := eq595 X0 X1
       grind)
    | exact resolve eq595 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq595
  have eq757 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq596 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq17292 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17293 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq17292
    | exact resolve eq17292 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17292
  have eq17304 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq17293
       have r₂ := eq27
       grind)
    | exact resolve eq17293 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17293
  have eq17308 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq17304
    | exact resolve eq17304 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17304
  have eq17310 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq17308 eq110
    | (have r₁ := eq110
       have r₂ := eq17308
       grind)
    | exact resolve eq110 eq17308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq17339 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq17308
  have eq17341 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq17310
  have eq17785 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq17341
       have r₂ := eq17339
       grind)
    | exact resolve eq17341 eq17339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17339 eq17341
  have eq17838 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq17785 eq97
    | exact resolve eq97 eq17785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq17785
  have eq17848 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq17838
  have eq17851 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq17848
       have r₂ := eq27
       grind)
    | exact resolve eq17848 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17848
  have eq17854 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq17851 eq119
    | exact resolve eq119 eq17851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17851
  have eq17895 : x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq28 eq17854
    | exact resolve eq17854 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17854
  have eq17896 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq17895
  have eq17900 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq109
       have i₂ := eq17896
       grind)
    | exact superpose eq17896 eq109
    | (have r₁ := eq109
       have r₂ := eq17896
       grind)
    | exact resolve eq109 eq17896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq17901 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq121
       have i₂ := eq17896
       grind)
    | exact superpose eq17896 eq121
    | exact resolve eq121 eq17896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17931 : x ≠ (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq17896
  have eq17933 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x x) := by grind
  clear eq17900
  have eq17947 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq17901
    | exact resolve eq17901 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17901
  have eq18531 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq17933
       have r₂ := eq17931
       grind)
    | exact resolve eq17933 eq17931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17931 eq17933
  have eq18542 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq757 x y
       have i₂ := eq18531
       grind)
    | exact superpose eq18531 eq757
    | (have j0 := eq757 x y
       grind)
    | exact resolve eq757 eq18531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757 eq18531
  have eq18546 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18542
       have i₂ := eq121
       grind)
    | exact superpose eq121 eq18542
    | exact resolve eq18542 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18542
  have eq18556 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq18546
    | exact resolve eq18546 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18546
  have eq18559 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq18556
       have r₂ := eq17947
       grind)
    | exact resolve eq18556 eq17947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18556
  have eq18560 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18559
       have i₂ := eq121
       grind)
    | exact superpose eq121 eq18559
    | exact resolve eq18559 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18559
  have eq18561 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18560
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18560
    | exact resolve eq18560 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18560
  have eq18562 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18561
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18561
    | exact resolve eq18561 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18561
  have eq18563 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq18562
    | exact resolve eq18562 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18562
  have eq18564 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18563
       have i₂ := eq121
       grind)
    | exact superpose eq121 eq18563
    | exact resolve eq18563 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18563
  have eq18565 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18564
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18564
    | exact resolve eq18564 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18564
  have eq20916 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq18565 eq17947
    | exact resolve eq17947 eq18565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17947 eq18565
  have eq20947 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq20916
  have eq20958 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq20947
       have r₂ := eq27
       grind)
    | exact resolve eq20947 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20947
  have eq21073 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20958 eq119
    | exact resolve eq119 eq20958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq20958
  have eq21135 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq21073
    | exact resolve eq21073 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq21073
  have eq21136 : x = (M.op x x) := by grind
  clear eq21135
  have eq21141 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq121
       have i₂ := eq21136
       grind)
    | exact superpose eq21136 eq121
    | exact resolve eq121 eq21136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq21151 : ∀ X0 : G, (M.op (M.op x (M.op x x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x
       have i₂ := eq21136
       grind)
    | exact superpose eq21136 eq14
    | exact resolve eq14 eq21136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21194 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq21151 X0
       have i₂ := eq21136
       grind)
    | exact superpose eq21136 eq21151
    | exact resolve eq21151 eq21136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21151
  have eq21203 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21141
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21141
    | exact resolve eq21141 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq21141
  have eq21223 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq21194 X0
       have i₂ := eq21136
       grind)
    | exact superpose eq21136 eq21194
    | exact resolve eq21194 eq21136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21136 eq21194
  have eq21252 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ x))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq21203 eq14
    | exact resolve eq14 eq21203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21294 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq21203 eq21252
    | exact resolve eq21252 eq21203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21252
  have eq21323 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq21203 eq21294
    | exact resolve eq21294 eq21203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21203 eq21294
  have eq21334 : y = (M.op x y) := by
    first
    | (have i₁ := eq21223 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21223
    | (have j0 := eq21223 y
       grind)
    | exact resolve eq21223 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq21223
  have eq21594 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21334 eq20
    | exact resolve eq20 eq21334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq21334
  have eq21721 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq21594
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21594
    | exact resolve eq21594 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq21594
  have eq21941 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21323 eq26
    | (have j1 := eq21323 (σ y)
       grind)
    | exact resolve eq26 eq21323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq21323
  have eq22074 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21721 eq21941
    | exact resolve eq21941 eq21721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21721 eq21941
  have eq22148 : False := by grind
  exact eq22148

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(X,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pyx_pxx_pyx_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  have eq52 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X1)) X3
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
  clear eq37
  have eq85 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq85
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq85
    | exact resolve eq85 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq92 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq91
    | exact resolve eq91 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq106 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq106 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq106
    | (have j0 := eq106 (σ X0)
       grind)
    | exact resolve eq106 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq106 x
       grind)
    | exact superpose eq106 eq44
    | (have j1 := eq106 x
       grind)
    | exact resolve eq44 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq407 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op (σ y) (M.op (σ x) (σ y)))))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq415 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) (M.op X3 (M.op X1 X3))) = (M.op (M.op X4 X0) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X1 X4 (M.op X1 (M.op X2 (M.op X0 X2))) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 x
       have i₂ := eq53 X2 X0 X1 x
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0)) X3) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op X1 X2)
       have i₂ := eq53 X1 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq494 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X4) = (M.op (M.op X1 (M.op X0 X1)) (M.op X2 (M.op (M.op X3 (M.op X4 X3)) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X3 (M.op X4 X3)) X4 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq54 X4 X1 X0 X3
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq869 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X3) X0)) X1)) X2) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq431 (M.op (M.op X1 (M.op (M.op X2 X3) X0)) X1) X2 X3
       have i₂ := eq431 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq431 eq431
    | exact resolve eq431 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq9193 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq407 (M.op X1 (M.op x X1)) sF4 sF3
       have i₂ := eq54 sF3 X1 x sF4
       grind)
    | exact superpose eq54 eq407
    | exact resolve eq407 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq407
  have eq15459 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq334 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq25246 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op (M.op X6 (M.op X4 (M.op X1 X4))) X6) = (M.op (M.op X0 X1) (M.op X5 (M.op (M.op X2 (M.op X0 X2)) X5))) := by
    intro X0 X1 X2 X4 X5 X6
    first
    | (have i₁ := eq415 (M.op X4 (M.op X1 X4)) (M.op X2 (M.op X0 X2)) x X5 X6
       have i₂ := eq494 X0 X2 x X4 X1
       grind)
    | exact superpose eq494 eq415
    | exact resolve eq415 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415 eq494
  have eq25395 : ∀ X0 X1 X2 X5 : G, (M.op (M.op X0 X1) (M.op X5 (M.op (M.op X2 (M.op X0 X2)) X5))) = X1 := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq25246 X0 X1 X2 x X5 x
       have i₂ := eq14 X1 x x
       grind)
    | exact superpose eq14 eq25246
    | exact resolve eq25246 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25246
  have eq86535 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op X1 X0) X1)) (σ y)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9193 (M.op (M.op sF4 sF2) (M.op (M.op X1 x) X1)) (M.op sF4 sF2)
       have i₂ := eq432 (M.op sF4 sF2) X1 x (M.op sF4 sF2)
       grind)
    | exact superpose eq432 eq9193
    | exact resolve eq9193 eq432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq152498 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op X0 X1) (σ y))) X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq9193 eq869
    | exact resolve eq869 eq9193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869 eq9193
  have eq424552 : ∀ X0 X1 : G, y = (M.op (M.op y x) (M.op X0 (M.op (M.op X1 (M.op y X1)) X0))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq25395 y y X1 X0
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq25395
    | exact resolve eq25395 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq424608 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq424552 x x
       have i₂ := eq25395 y x x x
       grind)
    | exact superpose eq25395 eq424552
    | exact resolve eq424552 eq25395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25395 eq424552
  have eq491897 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq424608 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq424608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491898 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq491897
    | exact resolve eq491897 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491897
  have eq491909 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq491898
       have r₂ := eq28
       grind)
    | exact resolve eq491898 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491898
  have eq492164 : (σ y) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ y) (σ x)) (σ y))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq491909 eq152498
    | exact resolve eq152498 eq491909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152498 eq491909
  have eq492169 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq86535 eq492164
    | exact resolve eq492164 eq86535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86535 eq492164
  have eq492395 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq492169
  have eq492812 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq492395
    | exact resolve eq492395 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492395
  have eq495886 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq492812 eq424608
    | exact resolve eq424608 eq492812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424608 eq492812
  have eq495888 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq495886
  have eq495890 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq495888
       have r₂ := eq28
       grind)
    | exact resolve eq495888 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495888
  have eq495893 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq338
       have i₂ := eq495890
       grind)
    | exact superpose eq495890 eq338
    | exact resolve eq338 eq495890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq495943 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq495890
  have eq496174 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq495893
  have eq496356 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq495943
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq495943
    | exact resolve eq495943 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495943
  have eq496379 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq496174
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq496174
    | exact resolve eq496174 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496174
  have eq500526 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq496356
       grind)
    | exact superpose eq496356 eq70
    | exact resolve eq70 eq496356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq496356
  have eq500544 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq500526
    | exact resolve eq500526 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500526
  have eq505581 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq496379
       have i₂ := eq106 sF2
       grind)
    | exact superpose eq106 eq496379
    | (have j1 := eq106 (σ x)
       grind)
    | exact resolve eq496379 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1169823 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq505581
  have eq1170453 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq1169823
    | exact resolve eq1169823 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169823
  have eq1174658 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1170453 eq500544
    | exact resolve eq500544 eq1170453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500544 eq1170453
  have eq1174660 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1174658
  have eq1174670 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1174660
       have r₂ := eq28
       grind)
    | exact resolve eq1174660 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174660
  have eq1174751 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq3347272 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1174751 eq496379
    | exact resolve eq496379 eq1174751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496379 eq1174751
  have eq3347307 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq3347272
  have eq3347338 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3347307 eq1174670
    | exact resolve eq1174670 eq3347307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174670 eq3347307
  have eq3348016 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq3347338
  have eq3348973 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq3348016 eq30
    | exact resolve eq30 eq3348016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3348016
  have eq3349588 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq3348973
    | exact resolve eq3348973 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3348973
  have eq3349589 : x = y := by grind
  clear eq3349588
  have eq3349622 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq3349589
       grind)
    | exact superpose eq3349589 eq19
    | exact resolve eq19 eq3349589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3349623 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq3349589
       grind)
    | exact superpose eq3349589 eq25
    | exact resolve eq25 eq3349589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq3349589
  have eq3350267 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3349623
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3349623
    | exact resolve eq3349623 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3349623
  have eq3350347 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3350267 eq27
    | exact resolve eq27 eq3350267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3350267
  have eq3351046 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq338
       have i₂ := eq3349622
       grind)
    | exact superpose eq3349622 eq338
    | exact resolve eq338 eq3349622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq3351187 : (M.op x (M.op x y)) = (k (M.op x y) x) := by grind
  have eq3352245 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq3351046
    | exact resolve eq3351046 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3351046
  have eq3352868 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq3398714 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3352245 eq106
    | (have j0 := eq106 (σ x)
       grind)
    | exact resolve eq106 eq3352245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq3398717 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3350347 eq3398714
    | exact resolve eq3398714 eq3350347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3398714
  have eq3398731 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3398717
       have r₂ := eq28
       grind)
    | exact resolve eq3398717 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3398717
  have eq3398737 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3350347 eq3398731
    | exact resolve eq3398731 eq3350347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3398731
  have eq3399132 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3398737 eq3352868
    | exact resolve eq3352868 eq3398737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3352868 eq3398737
  have eq3399137 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3350347 eq3399132
    | exact resolve eq3399132 eq3350347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3399132
  have eq3420158 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3399137 eq3352245
    | exact resolve eq3352245 eq3399137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3352245 eq3399137
  have eq3420169 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3420158
  have eq3420172 : x = (M.op x y) := by
    first
    | (have r₁ := eq3420169
       have r₂ := eq28
       grind)
    | exact resolve eq3420169 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3420169
  have eq3420183 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq3420172 eq21
    | exact resolve eq21 eq3420172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq3421015 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq3420172 eq3351187
    | exact resolve eq3351187 eq3420172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3351187
  have eq3421028 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq3421015
       have i₂ := eq3349622
       grind)
    | exact superpose eq3349622 eq3421015
    | exact resolve eq3421015 eq3349622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3349622 eq3421015
  have eq3421485 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3420183
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3420183
    | exact resolve eq3420183 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3420183
  have eq3421492 : x = (k x x) := by
    first
    | exact superpose eq3420172 eq3421028
    | exact resolve eq3421028 eq3420172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3420172 eq3421028
  have eq3424686 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq15459 x
       have i₂ := eq3421492
       grind)
    | exact superpose eq3421492 eq15459
    | (have j0 := eq15459 x
       grind)
    | exact resolve eq15459 eq3421492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15459 eq3421492
  have eq3424690 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3424686
  have eq3424701 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3424690
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3424690
    | exact resolve eq3424690 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3424690
  have eq3424718 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3350347 eq3424701
    | exact resolve eq3424701 eq3350347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3350347 eq3424701
  have eq3424733 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3421485 eq3424718
    | exact resolve eq3424718 eq3421485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3421485 eq3424718
  have eq3424746 : False := by grind
  exact eq3424746

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pxx_pyx_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  have eq51 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
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
  clear eq37
  have eq83 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq83
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq83
    | exact resolve eq83 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq89
    | exact resolve eq89 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq90
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq90
    | exact resolve eq90 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq105 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq105 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq105
    | (have j0 := eq105 (σ X0)
       grind)
    | exact resolve eq105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq105 x
       grind)
    | exact superpose eq105 eq44
    | (have j1 := eq105 x
       grind)
    | exact resolve eq44 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq416 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X0 X2)) (M.op X4 (M.op X3 X4))) = (M.op (M.op X5 (M.op X0 (M.op X1 (M.op X2 X1)))) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 X3 X5 (M.op X3 (M.op X0 X2)) X4
       have i₂ := eq53 X2 X3 X0 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op y X0))) = (M.op (M.op X1 (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 y X1 x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 y X1 x X0
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (M.op (σ y) X0))) = (M.op (M.op X1 (M.op (σ x) (σ y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ y) X1 (σ x) X0
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq426 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 X1) x X1 X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 x
       have i₂ := eq53 X2 X0 X1 x
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq803 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq426 X2 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq426
    | exact resolve eq426 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq805 : ∀ X0 : G, (M.op (M.op y (M.op x y)) (M.op X0 x)) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq426
    | exact resolve eq426 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq806 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq52 eq426
    | exact resolve eq426 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq827 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 x) X0)) := by
    intro X0
    first
    | exact superpose eq805 eq426
    | exact resolve eq426 eq805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq840 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq806 eq426
    | exact resolve eq426 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426 eq806
  have eq861 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) X0) x) := by
    intro X0
    first
    | (have i₁ := eq431 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq431
    | (have j0 := eq431 X0 x y
       grind)
    | exact resolve eq431 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq865 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq27 eq431
    | (have j0 := eq431 X0 (σ x) (σ y)
       grind)
    | exact resolve eq431 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq949 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | exact superpose eq827 eq14
    | exact resolve eq14 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq971 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq840 eq14
    | exact resolve eq14 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq15461 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq334 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq32744 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op x y)) X0) x) = (M.op (M.op X1 (M.op (M.op X2 y) X2)) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq416 (M.op X2 y) y X2 X1 X3 x
       have i₂ := eq419 (M.op X2 y) X0
       grind)
    | exact superpose eq419 eq416
    | exact resolve eq416 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq32747 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (σ x)) = (M.op (M.op X1 (M.op (M.op X2 (σ y)) X2)) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq420 eq416
    | exact resolve eq416 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416 eq420
  have eq33229 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (σ x)) = (M.op (M.op X1 (M.op (M.op (σ x) (σ y)) (σ x))) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X3
    first
    | exact superpose eq971 eq32747
    | (have j0 := eq32747 X0 X1 (σ x) X3
       grind)
    | exact resolve eq32747 eq971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971 eq32747
  have eq33232 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 (M.op x y)) X0) x) = (M.op (M.op X1 (M.op (M.op x y) x)) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq32744 X0 X1 x X3
       have i₂ := eq949 x
       grind)
    | (have i₁ := eq32744 X0 X1 x X3
       have i₂ := eq949 X0
       grind)
    | exact superpose eq949 eq32744
    | (have j0 := eq32744 X0 X1 x X3
       grind)
    | exact resolve eq32744 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949 eq32744
  have eq33558 : ∀ X1 X3 : G, (σ y) = (M.op (M.op X1 (M.op (M.op (σ x) (σ y)) (σ x))) (M.op X3 (M.op X1 X3))) := by
    intro X1 X3
    first
    | exact superpose eq865 eq33229
    | exact resolve eq33229 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865 eq33229
  have eq33559 : ∀ X1 X3 : G, y = (M.op (M.op X1 (M.op (M.op x y) x)) (M.op X3 (M.op X1 X3))) := by
    intro X1 X3
    first
    | exact superpose eq861 eq33232
    | exact resolve eq33232 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861 eq33232
  have eq126142 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq91 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126143 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq126142
    | exact resolve eq126142 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126142
  have eq126154 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq126143
       have r₂ := eq28
       grind)
    | exact resolve eq126143 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126143
  have eq126156 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq126154
    | exact resolve eq126154 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126154
  have eq126297 : (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq126156 eq33558
    | exact resolve eq33558 eq126156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126156
  have eq126302 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq126297
       have i₂ := eq803 sF4 sF2 sF2
       grind)
    | exact superpose eq803 eq126297
    | exact resolve eq126297 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126297
  have eq126433 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq126302
  have eq126656 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq126433
    | exact resolve eq126433 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126433
  have eq127520 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq126656 eq91
    | exact resolve eq91 eq126656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq126656
  have eq127528 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq127520
  have eq127530 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq127528
       have r₂ := eq28
       grind)
    | exact resolve eq127528 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127528
  have eq127930 : y = (M.op (M.op x (M.op (M.op x y) x)) (M.op x (M.op x y))) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq33559 x x
       have i₂ := eq127530
       grind)
    | exact superpose eq127530 eq33559
    | exact resolve eq33559 eq127530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33559 eq127530
  have eq127934 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq127930
       have i₂ := eq803 sF0 x x
       grind)
    | exact superpose eq803 eq127930
    | exact resolve eq127930 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127930
  have eq128055 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq127934
  have eq128275 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq128055
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq128055
    | exact resolve eq128055 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128055
  have eq129266 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq128275
       grind)
    | exact superpose eq128275 eq70
    | exact resolve eq70 eq128275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq128275
  have eq129284 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq129266
    | exact resolve eq129266 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129266
  have eq129993 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq129284 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq129284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129996 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq129993
    | exact resolve eq129993 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129993
  have eq130007 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq129996
       have r₂ := eq28
       grind)
    | exact resolve eq129996 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129996
  have eq130009 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq130007
    | exact resolve eq130007 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130007
  have eq312061 : (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq130009 eq33558
    | exact resolve eq33558 eq130009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33558 eq130009
  have eq312068 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq312061
       have i₂ := eq803 sF4 sF2 sF2
       grind)
    | exact superpose eq803 eq312061
    | exact resolve eq312061 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803 eq312061
  have eq312069 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq312068
  have eq312290 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq312069
  have eq312624 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq312290
    | exact resolve eq312290 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312290
  have eq312747 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq312624 eq129284
    | exact resolve eq129284 eq312624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129284 eq312624
  have eq312749 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq312747
  have eq312757 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq312749
       have r₂ := eq28
       grind)
    | exact resolve eq312749 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312749
  have eq312760 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq312757 eq30
    | exact resolve eq30 eq312757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq312757
  have eq313003 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq312760
    | exact resolve eq312760 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq312760
  have eq313004 : x = y := by grind
  clear eq313003
  have eq313010 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq313004
       grind)
    | exact superpose eq313004 eq19
    | exact resolve eq19 eq313004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq313011 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq313004
       grind)
    | exact superpose eq313004 eq25
    | exact resolve eq25 eq313004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq313004
  have eq313259 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq313011
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq313011
    | exact resolve eq313011 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313011
  have eq313272 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq313259 eq27
    | exact resolve eq27 eq313259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq313259
  have eq313573 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq338
       have i₂ := eq313010
       grind)
    | exact superpose eq313010 eq338
    | exact resolve eq338 eq313010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq313618 : (k (M.op x y) x) = (M.op x (M.op x y)) := by grind
  have eq313937 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq313573
    | exact resolve eq313573 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313573
  have eq314084 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq316650 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq313937 eq105
    | (have j0 := eq105 (σ x)
       grind)
    | exact resolve eq105 eq313937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq316651 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq313272 eq316650
    | exact resolve eq316650 eq313272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316650
  have eq316663 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq316651
       have r₂ := eq28
       grind)
    | exact resolve eq316651 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316651
  have eq316669 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq313272 eq316663
    | exact resolve eq316663 eq313272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316663
  have eq316811 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq316669 eq314084
    | exact resolve eq314084 eq316669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314084 eq316669
  have eq316814 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq313272 eq316811
    | exact resolve eq316811 eq313272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316811
  have eq317313 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq316814 eq313937
    | exact resolve eq313937 eq316814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313937 eq316814
  have eq317317 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq317313
  have eq317321 : x = (M.op x y) := by
    first
    | (have r₁ := eq317317
       have r₂ := eq28
       grind)
    | exact resolve eq317317 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317317
  have eq317329 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq317321 eq21
    | exact resolve eq21 eq317321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq317647 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq317321 eq313618
    | exact resolve eq313618 eq317321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313618
  have eq317652 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq317647
       have i₂ := eq313010
       grind)
    | exact superpose eq313010 eq317647
    | exact resolve eq317647 eq313010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313010 eq317647
  have eq317832 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq317329
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq317329
    | exact resolve eq317329 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317329
  have eq317835 : x = (k x x) := by
    first
    | exact superpose eq317321 eq317652
    | exact resolve eq317652 eq317321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317321 eq317652
  have eq319172 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq15461 x
       have i₂ := eq317835
       grind)
    | exact superpose eq317835 eq15461
    | (have j0 := eq15461 x
       grind)
    | exact resolve eq15461 eq317835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15461 eq317835
  have eq319176 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq319172
  have eq319186 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq319176
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq319176
    | exact resolve eq319176 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq319176
  have eq319198 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq313272 eq319186
    | exact resolve eq319186 eq313272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313272 eq319186
  have eq319209 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq317832 eq319198
    | exact resolve eq319198 eq317832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317832 eq319198
  have eq319218 : False := by grind
  exact eq319218
