import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation221`: `x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_pyx_pyx_pxy_pyx_Equation221 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law221 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law221.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  clear eq33 eq35
  have eq80 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
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
  have eq84 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq90 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq305 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq90 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq13
    | (have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq13 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq90 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq90 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq90 X0 X0
       grind)
    | exact resolve eq12 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq318 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq305 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq325 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq306 X0 X1
       have j1 := eq80 X0 (σ X1)
       grind)
    | (have r₁ := eq306 X0 X1
       have r₂ := eq80 X0 (σ X1)
       grind)
    | exact resolve eq306 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq326 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq318 X0 X1
       have j1 := eq80 X0 (σ X1)
       grind)
    | (have r₁ := eq318 X0 X1
       have r₂ := eq80 X0 (σ X1)
       grind)
    | exact resolve eq318 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq318
  have eq339 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq325 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq325
    | (have j0 := eq325 X0 X1
       grind)
    | exact resolve eq325 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq340 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq326 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq326
    | (have j0 := eq326 X0 X1
       grind)
    | exact resolve eq326 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq341 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq340 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq350 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq339 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq339
    | (have j0 := eq339 X0 X1
       grind)
    | exact resolve eq339 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq351 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq350 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq352 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq341 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq341
    | (have j0 := eq341 X0 X1
       grind)
    | exact resolve eq341 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq341
  have eq355 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq352 X0 X1
       have j1 := eq351 X0 X1
       grind)
    | (have r₁ := eq352 X0 X1
       have r₂ := eq351 X0 X1
       grind)
    | exact resolve eq352 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351 eq352
  have eq357 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq355 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq355
    | exact resolve eq355 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq355 x y
       grind)
    | exact superpose eq355 eq16
    | exact resolve eq16 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq455 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq357 X0 (τ X1)
       grind)
    | exact superpose eq357 eq18
    | exact resolve eq18 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq357
  have eq483 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq455 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq455
    | exact resolve eq455 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq497 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq483 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq483
    | exact resolve eq483 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq526 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq368
       have i₂ := eq497 x y
       grind)
    | exact superpose eq497 eq368
    | exact resolve eq368 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368 eq497
  have eq527 : False := by grind
  exact eq527

/-- `Equation221`: `x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyx_pxx_pyx_Equation221 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law221 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law221.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq41 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq42 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq49 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq41
    | (have j0 := eq41 x
       grind)
    | exact resolve eq41 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq55 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq16
    | exact resolve eq16 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq69 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq76 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq55
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq55
    | exact resolve eq55 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq77 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq76
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq76
    | exact resolve eq76 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq76
  have eq79 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X0) X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 (M.op X1 X0)
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq42 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq42
    | (have j0 := eq42 x
       grind)
    | exact resolve eq42 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq99
       have i₂ := eq79 y x
       grind)
    | exact superpose eq79 eq99
    | (have j1 := eq79 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq99 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq108
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq108
    | exact resolve eq108 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq114
    | exact resolve eq114 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq207 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq115 eq79
    | (have j0 := eq79 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq79 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq115
  have eq208 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq207
    | exact resolve eq207 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq211 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq208
       have r₂ := eq28
       grind)
    | exact resolve eq208 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq214 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq211 eq30
    | exact resolve eq30 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq211
  have eq227 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq214
    | exact resolve eq214 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq214
  have eq228 : x = y := by grind
  clear eq227
  have eq231 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq228
       grind)
    | exact superpose eq228 eq19
    | exact resolve eq19 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq232 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq228
       grind)
    | exact superpose eq228 eq25
    | exact resolve eq25 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq228
  have eq244 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq232
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq232
    | exact resolve eq232 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq232
  have eq274 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq244 eq27
    | exact resolve eq27 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq244
  have eq296 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq274 eq77
    | exact resolve eq77 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq274
  have eq300 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq296
       have i₂ := eq231
       grind)
    | exact superpose eq231 eq296
    | exact resolve eq296 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq296
  have eq341 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq300 eq15
    | exact resolve eq15 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq342 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq341
    | exact resolve eq341 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq341
  have eq343 : False := by grind
  exact eq343

/-- `Equation221`: `x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_Equation221 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law221 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law221.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X0 X0) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X1)) X0
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq15
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq38 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq24
  have eq55 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op X0 X1))) = X0 ∨ (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X1 (M.op X0 X1))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op X1 (M.op X0 X1))
       grind)
    | (have r₁ := eq13 X0 (M.op X1 (M.op X0 X1))
       have r₂ := eq9 X0 X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) = X0 ∨ (k X0 (M.op X1 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq78 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq79 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ (k X1 (k (τ (M.op (σ X0) (σ X0))) X0))) = (k (σ X1) (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0 X1
    grind
  clear eq22
  have eq102 : ∀ X0 X1 : G, (σ (k (k (τ (M.op (σ X0) (σ X0))) X0) X1)) = (k (M.op (σ X0) (M.op (σ X0) (σ X0))) (σ X1)) := by
    intro X0 X1
    grind
  clear eq23
  have eq126 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X0) = (k X0 (M.op X1 (M.op X0 X1))) ∨ (k X0 (M.op X1 (M.op X0 X1))) = X0 := by
    intro X0 X1
    grind
  clear eq56
  have eq127 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op X0 X1))) = X0 ∨ (k X0 (M.op X1 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq126 X0 X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq126
    | (have j0 := eq126 X0 X1
       grind)
    | exact resolve eq126 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq128 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq127 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq132 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k (M.op X1 (M.op X0 X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq128 (M.op X1 (M.op X0 X1)) X0
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq128
    | exact resolve eq128 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq128 (M.op X1 X1) (M.op X0 (M.op X1 X0))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq128
    | exact resolve eq128 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq138 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op (σ X0) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (M.op X1 (M.op (σ X0) X1))
       have i₂ := eq128 (σ X0) X1
       grind)
    | exact superpose eq128 eq30
    | exact resolve eq30 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op (τ X0) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (M.op X1 (M.op (τ X0) X1))
       have i₂ := eq128 (τ X0) X1
       grind)
    | exact superpose eq128 eq19
    | exact resolve eq19 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq142 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 (M.op (τ X0) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq139 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq139
    | exact resolve eq139 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq143 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (M.op (σ X0) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq138 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq138
    | exact resolve eq138 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq157 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 (M.op (τ (τ X0)) X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (σ (M.op X1 (M.op (τ (τ X0)) X1)))
       have i₂ := eq142 (τ X0) X1
       grind)
    | exact superpose eq142 eq19
    | exact resolve eq19 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq162 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op X1 (M.op (τ (τ X0)) X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq157 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq157
    | exact resolve eq157 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq182 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq78 X0 (k X1 (τ X0))
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq78
    | exact resolve eq78 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq211 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 (M.op (σ (σ X0)) X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (τ (M.op X1 (M.op (σ (σ X0)) X1)))
       have i₂ := eq143 (σ X0) X1
       grind)
    | exact superpose eq143 eq30
    | exact resolve eq30 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq218 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op X1 (M.op (σ (σ X0)) X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq211 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq211
    | exact resolve eq211 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq235 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op X1 (M.op (τ (τ (τ X0))) X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (σ (σ (M.op X1 (M.op (τ (τ (τ X0))) X1))))
       have i₂ := eq162 (τ X0) X1
       grind)
    | exact superpose eq162 eq19
    | exact resolve eq19 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (M.op X1 (M.op (τ (τ (τ X0))) X1)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq235 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq235
    | exact resolve eq235 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq300 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (M.op X1 (M.op (σ (σ (σ X0))) X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (τ (τ (M.op X1 (M.op (σ (σ (σ X0))) X1))))
       have i₂ := eq218 (σ X0) X1
       grind)
    | exact superpose eq218 eq30
    | exact resolve eq30 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq307 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (M.op X1 (M.op (σ (σ (σ X0))) X1)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq300 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq300
    | exact resolve eq300 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq423 : ∀ X0 : G, (k X0 (σ (k (σ (M.op (τ (τ X0)) (τ (τ X0)))) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq162 X0 (τ (τ X0))
       have i₂ := eq33 (τ X0)
       grind)
    | exact superpose eq33 eq162
    | exact resolve eq162 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq447 : ∀ X0 : G, (k X0 (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq423 X0
       have i₂ := eq20 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       grind)
    | exact superpose eq20 eq423
    | exact resolve eq423 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq878 : ∀ X0 : G, (k X0 (σ (σ (k (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))) (τ (τ X0)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq240 X0 (τ (τ (τ X0)))
       have i₂ := eq33 (τ (τ X0))
       grind)
    | exact superpose eq33 eq240
    | exact resolve eq240 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq240
  have eq921 : ∀ X0 : G, (k X0 (σ (k (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq878 X0
       have i₂ := eq20 (τ X0) (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))
       grind)
    | exact superpose eq20 eq878
    | exact resolve eq878 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq936 : ∀ X0 : G, (k X0 (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq921 X0
       have i₂ := eq20 X0 (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))
       grind)
    | exact superpose eq20 eq921
    | exact resolve eq921 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq921
  have eq959 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ X0)))) X1))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ X0)))) X1)))))
       have i₂ := eq307 (σ X0) X1
       grind)
    | exact superpose eq307 eq30
    | exact resolve eq30 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq970 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ X0)))) X1))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq959 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq959
    | exact resolve eq959 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq1723 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ (σ X0))))) X1)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (τ (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ (σ X0))))) X1))))))
       have i₂ := eq970 (σ X0) X1
       grind)
    | exact superpose eq970 eq30
    | exact resolve eq30 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq1736 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ (σ X0))))) X1)))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1723 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1723
    | exact resolve eq1723 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1723
  have eq2560 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (k (σ X0) X1) ∨ (k (σ X0) X1) = (k (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k (σ X0) X1) (σ X2)
       have i₂ := eq182 X0 X1 X2
       grind)
    | exact superpose eq182 eq13
    | (have j0 := eq13 (k (σ X0) X1) (σ X2)
       have j1 := eq182 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq182 X0 X1 X2
       grind)
    | exact resolve eq13 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2569 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (k (σ X0) X1) ∨ (k (σ X0) X1) = (k (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2560 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2560
  have eq2570 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (k (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2569 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2569
  have eq2571 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (k (k X0 (τ X1)) X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2570 X0 X1 X2
       have i₂ := eq29 X0 X1 X2
       grind)
    | exact superpose eq29 eq2570
    | (have j0 := eq2570 X0 X1 X2
       grind)
    | exact resolve eq2570 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2570
  have eq5068 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ (σ (σ X0)))))) X1))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (τ (τ (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ (σ (σ X0)))))) X1)))))))
       have i₂ := eq1736 (σ X0) X1
       grind)
    | exact superpose eq1736 eq30
    | exact resolve eq30 eq1736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1736
  have eq5098 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ (σ (σ X0)))))) X1))))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5068 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5068
    | exact resolve eq5068 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5068
  have eq9843 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq79 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq9844 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq9843 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9843
  have eq9848 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq9844 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9844
    | (have j0 := eq9844 X0
       grind)
    | exact resolve eq9844 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9844
  have eq9906 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq9848 X0
       grind)
    | exact superpose eq9848 eq38
    | (have j1 := eq9848 X0
       grind)
    | exact resolve eq38 eq9848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9848
  have eq9941 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq9906 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9906
    | (have j0 := eq9906 X0
       grind)
    | exact resolve eq9906 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9906
  have eq9942 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq9941 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9941
  have eq9962 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9942 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9942
    | exact resolve eq9942 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9995 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq9942 X0
       grind)
    | exact superpose eq9942 eq11
    | exact resolve eq11 eq9942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9996 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X0)) (σ X1)) = (σ (k (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (M.op (σ X0) (σ X0)) X1
       have i₂ := eq9942 X0
       grind)
    | exact superpose eq9942 eq19
    | exact resolve eq19 eq9942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10060 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9962 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq9962
    | exact resolve eq9962 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9962
  have eq10129 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (k (M.op (σ X0) (M.op (σ X0) (σ X0))) (σ (k (σ (σ (M.op (τ (τ (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))))) (τ (τ (τ (M.op (σ X0) (M.op (σ X0) (σ X0))))))))) (k (τ (M.op (σ X0) (σ X0))) X0)))) := by
    intro X0
    first
    | (have i₁ := eq936 (M.op (σ X0) (M.op (σ X0) (σ X0)))
       have i₂ := eq89 X0 (σ (σ (M.op (τ (τ (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))))) (τ (τ (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))))))))
       grind)
    | exact superpose eq89 eq936
    | exact resolve eq936 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq936
  have eq10143 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (k (k (τ (M.op (σ X0) (σ X0))) X0) (k (σ (σ (M.op (τ (τ (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))))) (τ (τ (τ (M.op (σ X0) (M.op (σ X0) (σ X0))))))))) (k (τ (M.op (σ X0) (σ X0))) X0)))) := by
    intro X0
    first
    | (have i₁ := eq10129 X0
       have i₂ := eq102 X0 (k (σ (σ (M.op (τ (τ (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))))) (τ (τ (τ (M.op (σ X0) (M.op (σ X0) (σ X0))))))))) (k (τ (M.op (σ X0) (σ X0))) X0))
       grind)
    | exact superpose eq102 eq10129
    | exact resolve eq10129 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq10129
  have eq10206 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (k (k (k X0 X0) X0) (k (σ (σ (M.op (τ (τ (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))))) (τ (τ (τ (M.op (σ X0) (M.op (σ X0) (σ X0))))))))) (k (k X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq10143 X0
       have i₂ := eq9942 X0
       grind)
    | exact superpose eq9942 eq10143
    | exact resolve eq10143 eq9942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10143
  have eq10245 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (k (k (k X0 X0) X0) (k (σ (σ (M.op (τ (τ (k (τ (M.op (σ X0) (σ X0))) X0))) (τ (τ (k (τ (M.op (σ X0) (σ X0))) X0)))))) (k (k X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq10206 X0
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq10206
    | exact resolve eq10206 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq10206
  have eq10279 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (k (k (k X0 X0) X0) (k (σ (σ (M.op (τ (τ (k (k X0 X0) X0))) (τ (τ (k (k X0 X0) X0)))))) (k (k X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq10245 X0
       have i₂ := eq9942 X0
       grind)
    | exact superpose eq9942 eq10245
    | exact resolve eq10245 eq9942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9942 eq10245
  have eq10299 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq10279 X0
       have i₂ := eq447 (k (k X0 X0) X0)
       grind)
    | exact superpose eq447 eq10279
    | exact resolve eq10279 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447 eq10279
  have eq10304 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq10299 X0
       have i₂ := eq9995 X0
       grind)
    | exact superpose eq9995 eq10299
    | exact resolve eq10299 eq9995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10299
  have eq10532 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq10060 X0
       grind)
    | exact superpose eq10060 eq11
    | exact resolve eq11 eq10060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10629 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq10532 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq10532
    | exact resolve eq10532 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10532
  have eq11151 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq10629 (τ X0)
       grind)
    | exact superpose eq10629 eq34
    | exact resolve eq34 eq10629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq11202 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11151 X0
       have i₂ := eq10060 X0
       grind)
    | exact superpose eq10060 eq11151
    | exact resolve eq11151 eq10060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10060 eq11151
  have eq11442 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ X0) (σ (k X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq9995 X0
       grind)
    | exact superpose eq9995 eq9
    | exact resolve eq9 eq9995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11471 : ∀ X0 : G, (σ X0) = (M.op (σ (k (k X0 X0) X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11442 X0
       have i₂ := eq10304 X0
       grind)
    | exact superpose eq10304 eq11442
    | exact resolve eq11442 eq10304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10304 eq11442
  have eq11529 : ∀ X0 : G, (σ X0) = (M.op (σ (k (M.op X0 X0) X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11471 X0
       have i₂ := eq10629 X0
       grind)
    | exact superpose eq10629 eq11471
    | exact resolve eq11471 eq10629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11471
  have eq11559 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ X0)) := by
    intro X0
    grind
  clear eq11529
  have eq12427 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (M.op (σ X0) (σ X0)) (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq132 (σ (M.op X0 (M.op X0 X0))) (σ X0)
       have i₂ := eq11559 X0
       grind)
    | exact superpose eq11559 eq132
    | exact resolve eq132 eq11559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq11559
  have eq12434 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (M.op (σ X0) (σ X0)) (σ (k (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq12427 X0
       have i₂ := eq9995 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq9995 eq12427
    | exact resolve eq12427 eq9995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12427
  have eq12462 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) (k (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq12434 X0
       have i₂ := eq9996 X0 (k (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq9996 eq12434
    | exact resolve eq12434 eq9996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9996 eq12434
  have eq12486 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq12462 X0
       have i₂ := eq10629 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq10629 eq12462
    | exact resolve eq12462 eq10629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12462
  have eq12504 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (M.op X0 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq12486 X0
       have i₂ := eq10629 X0
       grind)
    | exact superpose eq10629 eq12486
    | exact resolve eq12486 eq10629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12486
  have eq12517 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12504 X0
       have i₂ := eq134 X0 X0
       grind)
    | exact superpose eq134 eq12504
    | exact resolve eq12504 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq12504
  have eq12587 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq12517
  have eq12621 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq12587 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq12587
    | exact resolve eq12587 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12587
  have eq12651 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq12621
  have eq104390 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ (σ (σ (σ X0))))))) X1)))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (τ (τ (τ (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ (σ (σ (σ X0))))))) X1))))))))
       have i₂ := eq5098 (σ X0) X1
       grind)
    | exact superpose eq5098 eq30
    | exact resolve eq30 eq5098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq104506 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (τ (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ (σ (σ (σ X0))))))) X1)))))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq104390 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq104390
    | exact resolve eq104390 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104390
  have eq117971 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2571 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2571
  have eq117972 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq117971 X0 X1 X2
       have j1 := eq182 X0 X1 X2
       grind)
    | (have r₁ := eq117971 X0 X1 X2
       have r₂ := eq182 X0 X1 X2
       grind)
    | exact resolve eq117971 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq117971
  have eq118254 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (k X2 X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117972 X0 X1 X2
       have i₂ := eq9995 X2
       grind)
    | exact superpose eq9995 eq117972
    | (have j0 := eq117972 X0 X1 X2
       grind)
    | exact resolve eq117972 eq9995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9995 eq117972
  have eq118529 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq118254 X0 X1 X2
       have i₂ := eq10629 X2
       grind)
    | exact superpose eq10629 eq118254
    | (have j0 := eq118254 X0 X1 X2
       grind)
    | exact resolve eq118254 eq10629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10629 eq118254
  have eq443568 : ∀ X0 X1 X2 : G, (σ (k X0 X2)) = (M.op (σ X2) (k (σ X0) (τ (τ (τ (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ (σ (σ (σ X0))))))) X1)))))))))) ∨ (σ (M.op X2 X2)) = (k (σ X0) (τ (τ (τ (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ (σ (σ (σ X0))))))) X1))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq118529 X0 (τ (τ (τ (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ (σ (σ (σ X0))))))) X1)))))))) X2
       have i₂ := eq104506 X0 X1
       grind)
    | exact superpose eq104506 eq118529
    | (have j0 := eq118529 X0 (τ (τ (τ (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ (σ (σ (σ X0))))))) X1)))))))) X2
       grind)
    | exact resolve eq118529 eq104506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104506 eq118529
  have eq444623 : ∀ X0 X1 X2 : G, (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) ∨ (σ (M.op X2 X2)) = (k (σ X0) (τ (τ (τ (τ (τ (τ (M.op X1 (M.op (σ (σ (σ (σ (σ (σ (σ X0))))))) X1))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq443568 X0 X1 X2
       have i₂ := eq5098 (σ X0) X1
       grind)
    | exact superpose eq5098 eq443568
    | (have j0 := eq443568 X0 X1 X2
       grind)
    | exact resolve eq443568 eq5098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443568
  have eq444989 : ∀ X0 X2 : G, (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) ∨ (σ X0) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq444623 X0 x X2
       have i₂ := eq5098 (σ X0) x
       grind)
    | exact superpose eq5098 eq444623
    | (have j0 := eq444623 X0 x X2
       grind)
    | exact resolve eq444623 eq5098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5098 eq444623
  have eq446006 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq444989 (τ X0) x
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq444989
    | exact resolve eq444989 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446204 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq444989 y x
       grind)
    | exact superpose eq444989 eq16
    | (have j1 := eq444989 y x
       grind)
    | exact resolve eq16 eq444989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444989
  have eq446697 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq446006 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq446006
    | (have j0 := eq446006 X0 X1
       grind)
    | exact resolve eq446006 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq446006
  have eq449366 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq446697 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq446697
    | (have j0 := eq446697 X1 (τ X0)
       grind)
    | exact resolve eq446697 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446697
  have eq450234 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq449366 X0 X1
       have i₂ := eq11202 X0
       grind)
    | exact superpose eq11202 eq449366
    | (have j0 := eq449366 X0 X1
       grind)
    | exact resolve eq449366 eq11202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11202 eq449366
  have eq450505 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq450234 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq450234
    | (have j0 := eq450234 X0 X1
       grind)
    | exact resolve eq450234 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450234
  have eq456980 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq446204
       have i₂ := eq450505 x y
       grind)
    | exact superpose eq450505 eq446204
    | (have j1 := eq450505 x y
       grind)
    | exact resolve eq446204 eq450505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446204 eq450505
  have eq456989 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq456980
  have eq458381 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12651 x
       have i₂ := eq456989
       grind)
    | exact superpose eq456989 eq12651
    | exact resolve eq12651 eq456989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456989
  have eq458458 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq458381
       have r₂ := eq16
       grind)
    | exact resolve eq458381 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458381
  have eq458520 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq458458
       grind)
    | exact superpose eq458458 eq10
    | exact resolve eq10 eq458458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458458
  have eq459130 : y = (M.op x x) := by
    first
    | (have i₁ := eq458520
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq458520
    | exact resolve eq458520 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458520
  have eq461476 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12651 x
       have i₂ := eq459130
       grind)
    | exact superpose eq459130 eq12651
    | exact resolve eq12651 eq459130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12651 eq459130
  have eq461569 : False := by grind
  exact eq461569

/-- `Equation221`: `x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation221 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law221 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law221.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq352 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
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
  have eq354 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
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
  have eq355 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
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
  have eq422 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq355 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq355
    | exact resolve eq355 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq426 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq355 x (σ y)
       grind)
    | exact superpose eq355 eq16
    | (have j1 := eq355 x (σ y)
       grind)
    | exact resolve eq16 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq445 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq426
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq426
    | exact resolve eq426 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq455 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq422 X0 X1
       grind)
    | exact superpose eq422 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq422 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq422 X0 X1
       grind)
    | exact resolve eq13 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq475 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq455 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq483 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq475 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq475 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq475 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq515 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq483 X0 (τ X1)
       grind)
    | exact superpose eq483 eq18
    | (have j1 := eq483 X0 (τ X1)
       grind)
    | exact resolve eq18 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq521 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq483 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1386 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (τ X1)
       have i₂ := eq515 (τ X0) X1
       grind)
    | exact superpose eq515 eq19
    | (have j1 := eq515 (τ X0) X1
       grind)
    | exact resolve eq19 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq515
  have eq1395 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1386 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1386
    | (have j0 := eq1386 X0 X1
       grind)
    | exact resolve eq1386 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386
  have eq1412 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1395 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1395
    | (have j0 := eq1395 X0 X1
       grind)
    | exact resolve eq1395 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395
  have eq1417 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1412 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1412
    | (have j0 := eq1412 X0 X1
       grind)
    | exact resolve eq1412 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412
  have eq1483 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1417 X0 X1
       have i₂ := eq483 X0 X1
       grind)
    | exact superpose eq483 eq1417
    | (have j0 := eq1417 X0 X1
       have j1 := eq483 X0 X1
       grind)
    | exact resolve eq1417 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483 eq1417
  have eq1561 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1483 X0 X1
       have j1 := eq521 X1 X0
       grind)
    | (have r₁ := eq1483 X1 X0
       have r₂ := eq521 X0 X1
       grind)
    | exact resolve eq1483 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521 eq1483
  have eq1609 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq1561 (σ X0) X1
       grind)
    | exact superpose eq1561 eq23
    | (have j1 := eq1561 (σ X0) X1
       grind)
    | exact resolve eq23 eq1561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1561
  have eq1653 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1609 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1609
    | (have j0 := eq1609 X0 X1
       grind)
    | exact resolve eq1609 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1609
  have eq1677 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1653 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1653
    | (have j0 := eq1653 X0 X1
       grind)
    | exact resolve eq1653 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653
  have eq2036 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1677 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1677
    | exact resolve eq1677 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1677
  have eq2121 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2036 y x
       grind)
    | exact superpose eq2036 eq16
    | (have j1 := eq2036 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq2036 y x
       grind)
    | exact resolve eq16 eq2036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2036
  have eq2150 : x = (k y x) := by grind
  clear eq2121
  have eq2511 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq445
       have i₂ := eq422 x y
       grind)
    | exact superpose eq422 eq445
    | (have j1 := eq422 x y
       grind)
    | exact resolve eq445 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2512 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq2511
  have eq2513 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq2512
       have i₂ := eq2150
       grind)
    | exact superpose eq2150 eq2512
    | exact resolve eq2512 eq2150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2512
  have eq2514 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2513
       have i₂ := eq2150
       grind)
    | exact superpose eq2150 eq2513
    | exact resolve eq2513 eq2150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2513
  have eq2562 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq445
       have i₂ := eq2514
       grind)
    | exact superpose eq2514 eq445
    | exact resolve eq445 eq2514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445 eq2514
  have eq2575 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2562
  have eq2576 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2575
       have i₂ := eq2150
       grind)
    | exact superpose eq2150 eq2575
    | exact resolve eq2575 eq2150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2575
  have eq2577 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2576
  have eq2579 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2577
       grind)
    | exact superpose eq2577 eq16
    | exact resolve eq16 eq2577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2577
  have eq2604 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq2579
       have i₂ := eq422 x y
       grind)
    | exact superpose eq422 eq2579
    | (have j1 := eq422 x y
       grind)
    | exact resolve eq2579 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq2605 : (M.op x y) = (k y x) := by grind
  clear eq2604
  have eq2607 : x = (M.op x y) := by
    first
    | (have i₁ := eq2605
       have i₂ := eq2150
       grind)
    | exact superpose eq2150 eq2605
    | exact resolve eq2605 eq2150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2150 eq2605
  have eq2608 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2579
       have i₂ := eq2607
       grind)
    | exact superpose eq2607 eq2579
    | exact resolve eq2579 eq2607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2579 eq2607
  have eq2623 : False := by grind
  exact eq2623

/-- `Equation2291`: `x = (y ◇ (x ◇ (x ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation2291 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2291 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2291.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq66 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq69 (σ X0)
       grind)
    | exact superpose eq69 eq15
    | exact resolve eq15 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq74 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq74
    | exact resolve eq74 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq74
  have eq99 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq101 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq99 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq99
    | exact resolve eq99 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq104 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq101
  have eq240 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq242 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq245 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq240 X0 X1
       have i₂ := eq81 X0
       grind)
    | exact superpose eq81 eq240
    | (have j0 := eq240 X0 X1
       grind)
    | exact resolve eq240 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq660 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq245 x y
       grind)
    | exact superpose eq245 eq16
    | (have j1 := eq245 x y
       grind)
    | exact resolve eq16 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq1818 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq242 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq242
    | exact resolve eq242 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq1893 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1818 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1818
    | (have j0 := eq1818 X0 X1
       grind)
    | exact resolve eq1818 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1818
  have eq6270 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq660
       have i₂ := eq1893 y x
       grind)
    | exact superpose eq1893 eq660
    | (have j1 := eq1893 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq660
       have r₂ := eq1893 y x
       grind)
    | (have r₁ := eq660
       have r₂ := eq1893 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq660
       have r₂ := eq1893 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq660 eq1893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660 eq1893
  have eq6271 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq6270
  have eq6273 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6271
       grind)
    | exact superpose eq6271 eq16
    | exact resolve eq16 eq6271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6271
  have eq6274 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq6273
       have r₂ := eq81 x
       grind)
    | exact resolve eq6273 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6273
  have eq6276 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6274
       grind)
    | exact superpose eq6274 eq10
    | exact resolve eq10 eq6274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6274
  have eq6333 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6276
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6276
    | exact resolve eq6276 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6276
  have eq6336 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6333
       grind)
    | exact superpose eq6333 eq16
    | exact resolve eq16 eq6333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6333
  have eq6337 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq6336
       have r₂ := eq81 x
       grind)
    | exact resolve eq6336 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq6336
  have eq6518 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq6337
       grind)
    | exact superpose eq6337 eq10
    | exact resolve eq10 eq6337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6337
  have eq6577 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6518
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq6518
    | exact resolve eq6518 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6518
  have eq6578 : y = (M.op x x) := by grind
  clear eq6577
  have eq6589 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq104 x
       have i₂ := eq6578
       grind)
    | exact superpose eq6578 eq104
    | exact resolve eq104 eq6578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq6578
  have eq6639 : False := by grind
  exact eq6639

/-- `Equation2291`: `x = (y ◇ (x ◇ (x ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_x_pxy_Equation2291 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2291 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2291.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
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
  have eq284 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
  have eq303 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq284 X0
       have i₂ := eq273 X0
       grind)
    | exact superpose eq273 eq284
    | exact resolve eq284 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273 eq284
  have eq346 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq352 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq346 X0 X1
       have j1 := eq349 X0 X1
       grind)
    | (have r₁ := eq346 X0 X1
       have r₂ := eq349 X0 X1
       grind)
    | exact resolve eq346 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq349
  have eq414 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq352 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq352
    | exact resolve eq352 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq352 X1 X0
       grind)
    | exact superpose eq352 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq352 X1 (σ X1)
       grind)
    | (have r₁ := eq13 X1 (σ X0)
       have r₂ := eq352 X0 X1
       grind)
    | exact resolve eq13 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq434 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq427 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq441 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq434 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq434 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq434 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq471 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq441 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq441
    | exact resolve eq441 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq471 (τ X1) X0
       grind)
    | exact superpose eq471 eq18
    | (have j1 := eq471 (τ X1) X0
       grind)
    | exact resolve eq18 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq539 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq471 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq956 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq522 (τ X0) X1
       grind)
    | exact superpose eq522 eq17
    | (have j1 := eq522 (τ X0) X1
       grind)
    | exact resolve eq17 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq522
  have eq965 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq956 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq956
    | (have j0 := eq956 X0 X1
       grind)
    | exact resolve eq956 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq976 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq965 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq965
    | (have j0 := eq965 X0 X1
       grind)
    | exact resolve eq965 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq977 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq976 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq976
    | (have j0 := eq976 X0 X1
       grind)
    | exact resolve eq976 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
  have eq1033 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq977 X1 X0
       have i₂ := eq414 X0 X1
       grind)
    | exact superpose eq414 eq977
    | (have j1 := eq414 X1 X0
       grind)
    | exact resolve eq977 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1034 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) (τ (σ X1)))) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq977 X0 (σ X1)
       have i₂ := eq441 X0 X1
       grind)
    | exact superpose eq441 eq977
    | (have j0 := eq977 X0 (σ X1)
       have j1 := eq441 X0 X1
       grind)
    | exact resolve eq977 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441 eq977
  have eq1072 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1033 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033
  have eq1099 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (σ (M.op (τ X0) (τ (σ X1)))) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1034 X0 X1
       have j1 := eq539 X0 (σ X1)
       grind)
    | (have r₁ := eq1034 X0 X1
       have r₂ := eq539 X0 (σ X1)
       grind)
    | exact resolve eq1034 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539 eq1034
  have eq1117 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1099 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1099
    | (have j0 := eq1099 X0 X1
       grind)
    | exact resolve eq1099 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099
  have eq1225 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op (τ (σ x)) (τ (σ y)))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1072 (σ x) (σ y)
       grind)
    | exact superpose eq1072 eq16
    | (have j1 := eq1072 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1239 : (M.op (σ x) (σ y)) = (σ (M.op (τ (σ x)) y)) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq1225
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1225
    | exact resolve eq1225 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1257 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq1239
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1239
    | exact resolve eq1239 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239
  have eq1262 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have r₁ := eq1257
       have r₂ := eq16
       grind)
    | exact resolve eq1257 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257
  have eq2576 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq1117 (σ X0) X1
       grind)
    | exact superpose eq1117 eq28
    | (have j1 := eq1117 (σ X0) X1
       grind)
    | exact resolve eq28 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1117
  have eq2590 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2576 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2576
    | (have j0 := eq2576 X0 X1
       grind)
    | exact resolve eq2576 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2576
  have eq2606 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2590 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2590
    | (have j0 := eq2590 X0 X1
       grind)
    | exact resolve eq2590 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2590
  have eq2618 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2606 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2606
    | (have j0 := eq2606 X0 X1
       grind)
    | exact resolve eq2606 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2606
  have eq2656 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2618 x y
       grind)
    | exact superpose eq2618 eq16
    | (have j1 := eq2618 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2618 x y
       grind)
    | exact resolve eq16 eq2618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2618
  have eq2677 : x = (k x y) := by grind
  clear eq2656
  have eq2788 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq414 y x
       have i₂ := eq2677
       grind)
    | exact superpose eq2677 eq414
    | (have j0 := eq414 y x
       grind)
    | exact resolve eq414 eq2677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414 eq2677
  have eq2791 : x = (M.op x y) := by grind
  clear eq2788
  have eq2794 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1262
       have i₂ := eq2791
       grind)
    | exact superpose eq2791 eq1262
    | exact resolve eq1262 eq2791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262 eq2791
  have eq2801 : False := by grind
  exact eq2801

/-- `Equation2291`: `x = (y ◇ (x ◇ (x ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation2291 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2291 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2291.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
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
  clear eq22
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
  have eq284 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
  have eq290 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq273 (τ X0)
       grind)
    | exact superpose eq273 eq31
    | exact resolve eq31 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq297 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq290 X0
       have i₂ := eq273 X0
       grind)
    | exact superpose eq273 eq290
    | exact resolve eq290 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq303 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq284 X0
       have i₂ := eq273 X0
       grind)
    | exact superpose eq273 eq284
    | exact resolve eq284 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273 eq284
  have eq346 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq352 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq346 X0 X1
       have j1 := eq349 X0 X1
       grind)
    | (have r₁ := eq346 X0 X1
       have r₂ := eq349 X0 X1
       grind)
    | exact resolve eq346 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq349
  have eq363 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op (τ X0) X1) = X1 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (τ X0)
       have i₂ := eq297 X0
       grind)
    | exact superpose eq297 eq14
    | (have j0 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq14 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq297 X0
       grind)
    | exact superpose eq297 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq369 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq363 X0 X1
       have j1 := eq366 X0 X1
       grind)
    | (have r₁ := eq363 X0 X1
       have r₂ := eq366 X0 X1
       grind)
    | exact resolve eq363 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363 eq366
  have eq414 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq352 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq352
    | exact resolve eq352 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq462 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq414 X1 X0
       grind)
    | exact superpose eq414 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq414 X1 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq414 X0 X1
       grind)
    | exact resolve eq13 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq467 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq414 (σ x) (σ y)
       grind)
    | exact superpose eq414 eq16
    | (have j1 := eq414 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq472 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq462 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq476 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq467
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq467
    | exact resolve eq467 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq480 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq472 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq472 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq472 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq495 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq480 X1 (τ X0)
       grind)
    | exact superpose eq480 eq18
    | (have j1 := eq480 X1 (τ X0)
       grind)
    | exact resolve eq18 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq512 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq480 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1113 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq495 X1 (τ X0)
       grind)
    | exact superpose eq495 eq17
    | (have j1 := eq495 X1 (τ X0)
       grind)
    | exact resolve eq17 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq495
  have eq1120 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1113 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1113
    | (have j0 := eq1113 X0 X1
       grind)
    | exact resolve eq1113 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113
  have eq1131 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1120 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1120
    | (have j0 := eq1120 X0 X1
       grind)
    | exact resolve eq1120 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1132 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1131 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1131
    | (have j0 := eq1131 X0 X1
       grind)
    | exact resolve eq1131 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131
  have eq1191 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1132 X0 X1
       have i₂ := eq480 X0 X1
       grind)
    | exact superpose eq480 eq1132
    | (have j0 := eq1132 X1 X0
       have j1 := eq480 X1 X0
       grind)
    | exact resolve eq1132 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480 eq1132
  have eq1264 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1191 X0 X1
       have j1 := eq512 X1 X0
       grind)
    | (have r₁ := eq1191 X1 X0
       have r₂ := eq512 X0 X1
       grind)
    | exact resolve eq1191 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512 eq1191
  have eq1320 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq1264 X1 (σ X0)
       grind)
    | exact superpose eq1264 eq28
    | (have j1 := eq1264 X1 (σ X0)
       grind)
    | exact resolve eq28 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1264
  have eq1342 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1320 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1320
    | (have j0 := eq1320 X0 X1
       grind)
    | exact resolve eq1320 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320
  have eq1372 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1342 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1342
    | (have j0 := eq1342 X0 X1
       grind)
    | exact resolve eq1342 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342
  have eq2445 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1372 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1372
    | exact resolve eq1372 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2462 : ∀ X0 X1 : G, (M.op (τ X1) X0) = X0 ∨ (M.op (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq369 X1 X0
       have i₂ := eq1372 X0 X1
       grind)
    | exact superpose eq1372 eq369
    | (have j0 := eq369 X1 X0
       have j1 := eq1372 X0 X1
       grind)
    | exact resolve eq369 eq1372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq1372
  have eq2478 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2462 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2462
  have eq2523 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2445 x y
       grind)
    | exact superpose eq2445 eq16
    | (have j1 := eq2445 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2445 x y
       grind)
    | exact resolve eq16 eq2445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2445
  have eq2557 : y = (k y x) := by grind
  clear eq2523
  have eq2856 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2478 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2478
    | exact resolve eq2478 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2478
  have eq2983 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2856 x y
       grind)
    | exact superpose eq2856 eq16
    | (have j1 := eq2856 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2856 x y
       grind)
    | exact resolve eq16 eq2856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2856
  have eq3018 : y = (M.op x y) := by grind
  clear eq2983
  have eq4719 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq476
       have i₂ := eq3018
       grind)
    | exact superpose eq3018 eq476
    | exact resolve eq476 eq3018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq4726 : (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq4719
  have eq4730 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4726
       have i₂ := eq2557
       grind)
    | exact superpose eq2557 eq4726
    | exact resolve eq4726 eq2557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2557 eq4726
  have eq4736 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4730
       grind)
    | exact superpose eq4730 eq16
    | exact resolve eq16 eq4730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4730
  have eq4761 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq4736
       have i₂ := eq3018
       grind)
    | exact superpose eq3018 eq4736
    | exact resolve eq4736 eq3018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3018 eq4736
  have eq4762 : False := by grind
  exact eq4762

/-- `Equation2291`: `x = (y ◇ (x ◇ (x ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation2291 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2291 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2291.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  clear eq17
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
  have eq266 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X2) = X0 ∨ (k X2 X0) = (M.op X0 X2) := by
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
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
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
  have eq272 : ∀ X0 X1 X2 : G, (M.op X0 X2) = X0 ∨ (k X1 X0) = (M.op X0 X1) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq266 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
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
  have eq284 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
  have eq303 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq284 X0
       have i₂ := eq273 X0
       grind)
    | exact superpose eq273 eq284
    | exact resolve eq284 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273 eq284
  have eq346 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq352 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq346 X0 X1
       have j1 := eq349 X0 X1
       grind)
    | (have r₁ := eq346 X0 X1
       have r₂ := eq349 X0 X1
       grind)
    | exact resolve eq346 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq349
  have eq432 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq352 X0 (σ X1)
       grind)
    | exact superpose eq352 eq15
    | (have j1 := eq352 X0 (σ X1)
       grind)
    | exact resolve eq15 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq581 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X0 X2) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq272 X0 X2 X1
       grind)
    | exact superpose eq272 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq272 X0 X2 X0
       grind)
    | (have r₁ := eq13 X2 X0
       have r₂ := eq272 X0 X1 X2
       grind)
    | exact resolve eq13 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq598 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X0 X2) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq581 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq611 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X0 X2) ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq598 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq598 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq598 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq1124 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq432 x y
       grind)
    | exact superpose eq432 eq16
    | (have j1 := eq432 x y
       grind)
    | exact resolve eq16 eq432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1149 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq432 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq1186 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1149 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq1149
    | (have j0 := eq1149 (τ X1) (τ X0)
       grind)
    | exact resolve eq1149 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1194 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1186 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1186
    | (have j0 := eq1186 X0 X1
       grind)
    | exact resolve eq1186 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq1197 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1194 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1194
    | (have j0 := eq1194 X0 X1
       grind)
    | exact resolve eq1194 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194
  have eq1198 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1197 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1197
    | (have j0 := eq1197 X0 X1
       grind)
    | exact resolve eq1197 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197
  have eq1199 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1198 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1198
    | (have j0 := eq1198 X0 X1
       grind)
    | exact resolve eq1198 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq2809 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq611 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq2810 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2809 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2809
  have eq2869 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq1124
       have i₂ := eq2810 y x
       grind)
    | exact superpose eq2810 eq1124
    | (have j1 := eq2810 y x
       grind)
    | exact resolve eq1124 eq2810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq2870 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2810 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2810
  have eq2871 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by grind
  clear eq2869
  have eq2919 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq2870 (σ y) (σ x)
       have i₂ := eq2871
       grind)
    | exact superpose eq2871 eq2870
    | (have j0 := eq2870 (σ y) (σ x)
       grind)
    | (have r₁ := eq2870 (σ y) (σ x)
       have r₂ := eq2871
       grind)
    | exact resolve eq2870 eq2871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2871
  have eq2922 : (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) := by grind
  clear eq2919
  have eq2924 : x = (k y x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq2922
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2922
    | exact resolve eq2922 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2922
  have eq2947 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq1149 x y
       have i₂ := eq2924
       grind)
    | exact superpose eq2924 eq1149
    | (have j0 := eq1149 x y
       grind)
    | (have r₁ := eq1149 x y
       have r₂ := eq2924
       grind)
    | exact resolve eq1149 eq2924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2924
  have eq2958 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq2947
  have eq2961 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq1149 x y
       grind)
    | (have r₁ := eq2958
       have r₂ := eq1149 x y
       grind)
    | exact resolve eq2958 eq1149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149 eq2958
  have eq2965 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2961
       grind)
    | exact superpose eq2961 eq16
    | exact resolve eq16 eq2961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2966 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2870 (σ y) (σ x)
       have i₂ := eq2961
       grind)
    | exact superpose eq2961 eq2870
    | (have j0 := eq2870 (σ y) (σ x)
       grind)
    | (have r₁ := eq2870 (σ y) (σ x)
       have r₂ := eq2961
       grind)
    | exact resolve eq2870 eq2961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2870 eq2961
  have eq2969 : (σ x) = (k (σ y) (σ x)) := by grind
  clear eq2966
  have eq2971 : (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq2969
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2969
    | exact resolve eq2969 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2969
  have eq2987 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq2971
       grind)
    | exact superpose eq2971 eq10
    | exact resolve eq10 eq2971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2971
  have eq3038 : x = (k y x) := by
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
  have eq3057 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1199 y x
       have i₂ := eq3038
       grind)
    | exact superpose eq3038 eq1199
    | (have j0 := eq1199 y x
       grind)
    | (have r₁ := eq1199 y x
       have r₂ := eq3038
       grind)
    | exact resolve eq1199 eq3038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199 eq3038
  have eq3066 : x = (M.op x y) := by grind
  clear eq3057
  have eq3070 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2965
       have i₂ := eq3066
       grind)
    | exact superpose eq3066 eq2965
    | exact resolve eq2965 eq3066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2965 eq3066
  have eq3079 : False := by grind
  exact eq3079
