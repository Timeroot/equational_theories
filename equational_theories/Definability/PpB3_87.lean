import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq53 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq53 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq54 (σ X0)
       grind)
    | exact superpose eq54 eq15
    | exact resolve eq15 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq56
  have eq79 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq91 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq85
  have eq268 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq286 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq268 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq290 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq286 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq286 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq286 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq300 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq290 X0 X1
       have j1 := eq79 X0 (σ X1)
       grind)
    | (have r₁ := eq290 X0 X1
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq290 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq290
  have eq308 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq300 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq300
    | (have j0 := eq300 X0 X1
       grind)
    | exact resolve eq300 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq309 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq308 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq361 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
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
  have eq372 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq309 x y
       grind)
    | exact superpose eq309 eq16
    | exact resolve eq16 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq422 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq361 X0 (τ X1)
       grind)
    | exact superpose eq361 eq17
    | exact resolve eq17 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq361
  have eq438 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq422 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq422
    | exact resolve eq422 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq446 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq438 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq438
    | exact resolve eq438 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq545 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq372
       have i₂ := eq446 x y
       grind)
    | exact superpose eq446 eq372
    | exact resolve eq372 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq446
  have eq546 : False := by grind
  exact eq546

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
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
  have eq50 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
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
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq72 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = (k y x) := by
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
  have eq73 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq90
    | (have j0 := eq90 (σ X0) (σ X1)
       grind)
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq69
       have i₂ := eq90 y x
       grind)
    | exact superpose eq90 eq69
    | (have j1 := eq90 y x
       grind)
    | exact resolve eq69 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101
    | exact resolve eq101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq116 eq90
    | (have j0 := eq90 (σ y) (σ x)
       grind)
    | exact resolve eq90 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq119
    | exact resolve eq119 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq123 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq120
       have r₂ := eq27
       grind)
    | exact resolve eq120 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq125 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq123
    | exact resolve eq123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq125 eq27
    | exact resolve eq27 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq125 eq73
    | (have r₁ := eq73
       have r₂ := eq125
       grind)
    | exact resolve eq73 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq125
  have eq345 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq344
  have eq454 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq94 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq613 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X2 X0 X1
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1655 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 x
       have i₂ := eq613 X1 x X0
       grind)
    | exact superpose eq613 eq14
    | exact resolve eq14 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq4462 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq454 x y
       have i₂ := eq69
       grind)
    | exact superpose eq69 eq454
    | (have j0 := eq454 x y
       grind)
    | exact resolve eq454 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq4477 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4462
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4462
    | exact resolve eq4462 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4462
  have eq4501 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq4477
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4477
    | exact resolve eq4477 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4477
  have eq4522 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq4501
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4501
    | exact resolve eq4501 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4501
  have eq4535 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq4522
    | exact resolve eq4522 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4522
  have eq7395 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq345 eq116
    | exact resolve eq116 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq7403 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq7395
  have eq7408 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq7403
       have r₂ := eq127
       grind)
    | exact resolve eq7403 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq7403
  have eq7474 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7408 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq7408
       grind)
    | exact resolve eq13 eq7408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7408
  have eq7481 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq7474 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7474
  have eq12672 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7481 eq116
    | exact resolve eq116 eq7481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq7481
  have eq12692 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12672
  have eq12704 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12692
    | exact resolve eq12692 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq12692
  have eq12706 : x = (M.op x y) := by
    first
    | (have r₁ := eq12704
       have r₂ := eq27
       grind)
    | exact resolve eq12704 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12704
  have eq12708 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq12706 eq20
    | exact resolve eq20 eq12706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12710 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq12706 eq50
    | exact resolve eq50 eq12706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq12712 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq12706 eq72
    | (have r₁ := eq72
       have r₂ := eq12706
       grind)
    | exact resolve eq72 eq12706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq12728 : x = (k y x) ∨ x = (M.op x x) := by grind
  clear eq12712
  have eq12745 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq12710 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12710
    | (have j0 := eq12710 X0
       grind)
    | exact resolve eq12710 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12710
  have eq12747 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq12708
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12708
    | exact resolve eq12708 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12708
  have eq12754 : ∀ X0 : G, y = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq12706 eq12745
    | exact resolve eq12745 eq12706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12706 eq12745
  have eq12843 : (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12747 eq4535
    | exact resolve eq4535 eq12747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4535
  have eq12867 : (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq12843
       have r₂ := eq27
       grind)
    | exact resolve eq12843 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq12843
  have eq16059 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq12728
       grind)
    | exact superpose eq12728 eq69
    | exact resolve eq69 eq12728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12728
  have eq16075 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq12747 eq16059
    | exact resolve eq16059 eq12747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16059
  have eq16081 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16075
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16075
    | exact resolve eq16075 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16075
  have eq16086 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq12747 eq16081
    | exact resolve eq16081 eq12747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16081
  have eq16091 : x = (M.op x x) := by
    first
    | (have r₁ := eq16086
       have r₂ := eq12867
       grind)
    | exact resolve eq16086 eq12867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16086
  have eq16113 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq16091
       grind)
    | exact superpose eq16091 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq16091
       grind)
    | exact resolve eq13 eq16091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16128 : x = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq1655 x x
       have i₂ := eq16091
       grind)
    | exact superpose eq16091 eq1655
    | exact resolve eq1655 eq16091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1655 eq16091
  have eq16133 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq16113 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16113
  have eq16138 : x = y := by
    first
    | (have i₁ := eq16128
       have i₂ := eq12754 x
       grind)
    | exact superpose eq12754 eq16128
    | exact resolve eq16128 eq12754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12754 eq16128
  have eq16171 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq16138
       grind)
    | exact superpose eq16138 eq24
    | exact resolve eq24 eq16138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq16138
  have eq16227 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq16171
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16171
    | exact resolve eq16171 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq16171
  have eq16250 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12747 eq16227
    | exact resolve eq16227 eq12747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16227
  have eq16367 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq16250 eq12867
    | exact resolve eq12867 eq16250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12867
  have eq16433 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq16133 y
       grind)
    | exact superpose eq16133 eq69
    | exact resolve eq69 eq16133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq16133
  have eq16467 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq12747 eq16433
    | exact resolve eq16433 eq12747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12747 eq16433
  have eq16486 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq16250 eq16467
    | exact resolve eq16467 eq16250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16250 eq16467
  have eq16496 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq16486
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16486
    | exact resolve eq16486 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq16486
  have eq16504 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16496
    | exact resolve eq16496 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq16496
  have eq16508 : False := by grind
  exact eq16508

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pyx_pxx_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
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
  have eq31 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 (M.op (M.op X0 X1) X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) X1) (M.op X2 (M.op (M.op X0 X1) X1)) X2
       have i₂ := eq9 X1 (M.op X2 (M.op (M.op X0 X1) X1)) X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op (M.op X0 X1) X1)) (M.op (M.op X0 X1) X1)) = (M.op X1 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X2 (M.op (M.op X0 X1) X1) (M.op X2 (M.op (M.op X0 X1) X1))
       have i₂ := eq9 X1 (M.op X2 (M.op (M.op X0 X1) X1)) X0
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq14 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq946 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X1 X2 X1 X0
       have i₂ := eq9 X1 X1 X0
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq1083 : ∀ X0 X2 : G, (M.op X2 (M.op X0 (M.op X0 X2))) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X2 X2 x
       have i₂ := eq946 x X2 X0
       grind)
    | exact superpose eq946 eq9
    | exact resolve eq9 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1099 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X1 (M.op (M.op X2 X1) X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X0 X1 (M.op X0 X1)
       have i₂ := eq946 X2 X1 (M.op X0 X1)
       grind)
    | exact superpose eq946 eq31
    | exact resolve eq31 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq1108 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 X1) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1099 X0 X1 X2
       have i₂ := eq31 X2 X1 X1
       grind)
    | exact superpose eq31 eq1099
    | exact resolve eq1099 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1099
  have eq1144 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1083 X0 (M.op X0 X0)
       have i₂ := eq1083 X0 X0
       grind)
    | exact superpose eq1083 eq1083
    | exact resolve eq1083 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq2123 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1108 X1 X1 X0
       have i₂ := eq1144 X1
       grind)
    | exact superpose eq1144 eq1108
    | exact resolve eq1108 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108 eq1144
  have eq2682 : ∀ X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X2 (M.op X1 X1)) (M.op X1 X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq58 x X1 X2
       have i₂ := eq2123 x X1
       grind)
    | exact superpose eq2123 eq58
    | exact resolve eq58 eq2123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq2683 : ∀ X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = (M.op X1 (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq2682 X1 x
       have i₂ := eq2123 x (M.op X1 X1)
       grind)
    | exact superpose eq2123 eq2682
    | exact resolve eq2682 eq2123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2123 eq2682
  have eq2751 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq2683
  have eq2780 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2751 X0
       have j1 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq2751 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq2751 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2751
  have eq2794 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2780 X1
       have i₂ := eq106 X0 X1
       grind)
    | (have i₁ := eq2780 X0
       have i₂ := eq106 (M.op X0 X0) X1
       grind)
    | exact superpose eq106 eq2780
    | (have j1 := eq106 X0 X1
       grind)
    | exact resolve eq2780 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq2780
  have eq2809 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2794 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2794
  have eq2838 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2809 (σ X0) (σ X1)
       grind)
    | exact superpose eq2809 eq15
    | exact resolve eq15 eq2809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2853 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2838 X0 X1
       have i₂ := eq2809 X0 X1
       grind)
    | exact superpose eq2809 eq2838
    | exact resolve eq2838 eq2809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2809 eq2838
  have eq3032 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2853 y x
       grind)
    | exact superpose eq2853 eq16
    | (have r₁ := eq16
       have r₂ := eq2853 y x
       grind)
    | exact resolve eq16 eq2853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2853
  have eq3044 : False := by grind
  exact eq3044

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyy_pyx_Equation723 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq64 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
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
  clear eq24
  have eq116 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq117 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq116 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq116
    | (have j0 := eq116 X0 X1
       grind)
    | exact resolve eq116 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq142 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq117 y x
       grind)
    | exact superpose eq117 eq16
    | (have j1 := eq117 y x
       grind)
    | exact resolve eq16 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq159 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (M.op (τ (M.op X0 X0)) (τ X0)))) := by
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
  have eq621 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq142
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq142
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq142
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq142
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq142 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq622 : x = y ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op x x) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq621
  have eq669 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ X0))) = (M.op X1 (M.op X1 (τ X0))) := by
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
  clear eq73 eq108
  have eq1034 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (M.op X0 (M.op X0 (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq159 X1 (τ X1)
       have i₂ := eq669 X1 X0
       grind)
    | exact superpose eq669 eq159
    | exact resolve eq159 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq669
  have eq1056 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1034 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1034
    | exact resolve eq1034 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq1197 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1056 (M.op X0 X0) X0
       have i₂ := eq1056 X0 X0
       grind)
    | exact superpose eq1056 eq1056
    | exact resolve eq1056 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1204 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 (M.op X1 (M.op X1 X0)) X1 X0
       have i₂ := eq1056 X0 X1
       grind)
    | exact superpose eq1056 eq25
    | exact resolve eq25 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1205 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op X2 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 (M.op X2 X0)) X1 X0
       have i₂ := eq1056 X0 X2
       grind)
    | exact superpose eq1056 eq9
    | exact resolve eq9 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1208 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1205 X0 X1 X2
       have i₂ := eq1056 X0 X2
       grind)
    | exact superpose eq1056 eq1205
    | exact resolve eq1205 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq1209 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1204 X0 X1 X2
       have i₂ := eq1056 X0 X1
       grind)
    | exact superpose eq1056 eq1204
    | exact resolve eq1204 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204
  have eq1237 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1 X0
       have i₂ := eq1197 X0
       grind)
    | exact superpose eq1197 eq25
    | exact resolve eq25 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq1238 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq1197 X0
       grind)
    | exact superpose eq1197 eq9
    | exact resolve eq9 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1239 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1056 X0 (M.op X0 X0)
       have i₂ := eq1197 X0
       grind)
    | exact superpose eq1197 eq1056
    | exact resolve eq1056 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056
  have eq1300 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1238 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq1238
    | exact resolve eq1238 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1843 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq97 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X0
       have i₂ := eq1239 X0
       grind)
    | exact superpose eq1239 eq97
    | exact resolve eq97 eq1239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq1854 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1843 X0 X1
       have i₂ := eq1239 X0
       grind)
    | exact superpose eq1239 eq1843
    | exact resolve eq1843 eq1239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843
  have eq1862 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1854 X0 X1
       have i₂ := eq1237 X0 (M.op X0 X0)
       grind)
    | exact superpose eq1237 eq1854
    | exact resolve eq1854 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237 eq1854
  have eq2172 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X0)))) = (M.op X4 (M.op X4 (M.op (M.op X2 (M.op X0 X0)) (M.op X1 (M.op X0 (M.op X2 (M.op X0 X0))))))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq101 X0 X1 X2 X1 X4
       have i₂ := eq1862 X0 X1
       grind)
    | exact superpose eq1862 eq101
    | exact resolve eq101 eq1862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq2287 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))))) = (M.op (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) (M.op (M.op X0 X0) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq2172 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)) X0 (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq2172 X0 (M.op X0 X0) (M.op X0 X0) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))
       grind)
    | exact superpose eq2172 eq2172
    | exact resolve eq2172 eq2172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2172
  have eq2342 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq2287 X0
       have i₂ := eq1239 X0
       grind)
    | exact superpose eq1239 eq2287
    | exact resolve eq2287 eq1239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239 eq2287
  have eq2354 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2342 X0
       have i₂ := eq1197 X0
       grind)
    | exact superpose eq1197 eq2342
    | exact resolve eq2342 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2342
  have eq2356 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2354 X0
       have i₂ := eq1197 (M.op X0 X0)
       grind)
    | exact superpose eq1197 eq2354
    | exact resolve eq2354 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197 eq2354
  have eq2422 : ∀ X0 X2 X3 : G, (M.op (M.op X3 (M.op X2 (M.op X0 (M.op X2 X2)))) (M.op X2 (M.op X0 (M.op X2 X2)))) = (M.op (M.op X0 (M.op X2 X2)) (M.op X2 (M.op X0 (M.op X2 X2)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq112 X0 x X0 X3
       have i₂ := eq1862 X0 x
       grind)
    | exact superpose eq1862 eq112
    | exact resolve eq112 eq1862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq2423 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op X2 X2)) (M.op X2 (M.op X0 (M.op X2 X2)))) = (M.op (M.op X2 (M.op X0 (M.op X2 X2))) (M.op X2 (M.op X0 (M.op X2 X2)))) := by
    intro X0 X2
    first
    | (have i₁ := eq2422 X0 X2 x
       have i₂ := eq1862 (M.op X2 (M.op X0 (M.op X2 X2))) x
       grind)
    | exact superpose eq1862 eq2422
    | exact resolve eq2422 eq1862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2422
  have eq2578 : ∀ X0 : G, (M.op (σ X0) (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0))) = (M.op (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)) (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2423 (M.op (σ (M.op X0 X0)) (σ X0)) (M.op (σ (M.op X0 X0)) (σ X0))
       have i₂ := eq64 X0 (M.op (σ (M.op X0 X0)) (σ X0))
       grind)
    | exact superpose eq64 eq2423
    | exact resolve eq2423 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2423
  have eq2635 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2578 X0
       have i₂ := eq1862 (σ X0) (σ (M.op X0 X0))
       grind)
    | exact superpose eq1862 eq2578
    | exact resolve eq2578 eq1862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1862 eq2578
  have eq2645 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2635 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq2635
    | exact resolve eq2635 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2635
  have eq2649 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2645 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq2645
    | exact resolve eq2645 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2645
  have eq3343 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2356 (M.op X0 X0)
       have i₂ := eq2356 X0
       grind)
    | exact superpose eq2356 eq2356
    | exact resolve eq2356 eq2356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3403 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq3343 X0
       have i₂ := eq1209 X0 X0 X0
       grind)
    | exact superpose eq1209 eq3343
    | exact resolve eq3343 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209 eq3343
  have eq3406 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2649 X0
       have i₂ := eq2356 X0
       grind)
    | exact superpose eq2356 eq2649
    | exact resolve eq2649 eq2356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2356 eq2649
  have eq3441 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ (M.op X0 X0)))) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1208 (σ (M.op X0 X0)) (σ X0) X1
       have i₂ := eq3406 X0
       grind)
    | exact superpose eq3406 eq1208
    | exact resolve eq1208 eq3406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3406
  have eq3451 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq3441 X0 x
       have i₂ := eq1300 X0 x
       grind)
    | exact superpose eq1300 eq3441
    | exact resolve eq3441 eq1300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3441
  have eq4492 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op X1 (M.op X1 (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq3403 X0
       grind)
    | exact superpose eq3403 eq64
    | exact resolve eq64 eq3403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq3403
  have eq4551 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4492 X0 X1
       have i₂ := eq3451 X0
       grind)
    | exact superpose eq3451 eq4492
    | exact resolve eq4492 eq3451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3451 eq4492
  have eq5328 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (τ (M.op X0 (M.op X0 (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 (M.op X1 X1))
       have i₂ := eq4551 X1 X0
       grind)
    | exact superpose eq4551 eq10
    | exact resolve eq10 eq4551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4551
  have eq6530 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (τ (M.op X2 (M.op X2 (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5328 X2 X1
       have i₂ := eq1208 X1 X0 X1
       grind)
    | (have i₁ := eq5328 X2 X1
       have i₂ := eq1208 X1 X1 X0
       grind)
    | exact superpose eq1208 eq5328
    | exact resolve eq5328 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208 eq5328
  have eq7549 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op x x) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq622
       grind)
    | exact superpose eq622 eq16
    | exact resolve eq16 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq7550 : (M.op y y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq7549
       have r₂ := eq22 x
       grind)
    | exact resolve eq7549 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7549
  have eq728630 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ (M.op x x)))) ∨ (σ x) = (σ y) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq1300 y X0
       have i₂ := eq7550
       grind)
    | exact superpose eq7550 eq1300
    | exact resolve eq1300 eq7550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7550
  have eq729145 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq728630 x
       have i₂ := eq1300 x x
       grind)
    | exact superpose eq1300 eq728630
    | exact resolve eq728630 eq1300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728630
  have eq729146 : (σ x) = (σ y) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq729145
  have eq735630 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq22 y
       have i₂ := eq729146
       grind)
    | exact superpose eq729146 eq22
    | exact resolve eq22 eq729146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729146
  have eq736121 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq735630
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq735630
    | exact resolve eq735630 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735630
  have eq736122 : (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq736121
  have eq739111 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op y y))) = (τ (M.op X1 (M.op X1 (σ (M.op x x))))) := by
    intro X0 X1
    first
    | (have i₁ := eq6530 X0 (M.op y y) X1
       have i₂ := eq736122
       grind)
    | exact superpose eq736122 eq6530
    | exact resolve eq6530 eq736122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6530 eq736122
  have eq739256 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op y y))) = (τ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq739111 X0 x
       have i₂ := eq1300 x x
       grind)
    | exact superpose eq1300 eq739111
    | exact resolve eq739111 eq1300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300 eq739111
  have eq739556 : ∀ X0 : G, x = (M.op X0 (M.op X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq739256 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq739256
    | exact resolve eq739256 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739256
  have eq739777 : x = y := by
    first
    | (have i₁ := eq739556 x
       have i₂ := eq1238 y x
       grind)
    | exact superpose eq1238 eq739556
    | exact resolve eq739556 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238 eq739556
  have eq739870 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq739777
       grind)
    | exact superpose eq739777 eq16
    | exact resolve eq16 eq739777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739777
  have eq739871 : False := by grind
  exact eq739871

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation723 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq400 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3264 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq400 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq400 X0 X1
       grind)
    | exact superpose eq400 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq400 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq400 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq400 X0 X1
       grind)
    | exact resolve eq13 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq3281 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3264 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3264
  have eq3282 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3281 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3281
  have eq3295 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3282 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3282
    | (have j0 := eq3282 X0 X1
       grind)
    | exact resolve eq3282 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3282
  have eq3296 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq3295 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3295
  have eq13924 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3296 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq3296
    | (have j0 := eq3296 (τ X0) (τ X1)
       grind)
    | exact resolve eq3296 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq13982 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13924 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13924
    | (have j0 := eq13924 X0 X1
       grind)
    | exact resolve eq13924 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13924
  have eq14000 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13982 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq13982
    | (have j0 := eq13982 X0 X1
       grind)
    | exact resolve eq13982 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13982
  have eq14005 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14000 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq14000
    | (have j0 := eq14000 X0 X1
       grind)
    | exact resolve eq14000 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14000
  have eq14010 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14005 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq14005
    | (have j0 := eq14005 X0 X1
       grind)
    | exact resolve eq14005 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14005
  have eq14015 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14010 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14010
    | (have j0 := eq14010 X0 X1
       grind)
    | exact resolve eq14010 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14010
  have eq14024 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3296 X0 X1
       have i₂ := eq14015 X1 X0
       grind)
    | exact superpose eq14015 eq3296
    | (have j0 := eq3296 X0 X1
       have j1 := eq14015 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq3296 eq14015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3296 eq14015
  have eq321286 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14024 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14024
  have eq335942 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq321286 x y
       grind)
    | exact superpose eq321286 eq16
    | (have j1 := eq321286 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq321286 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq321286 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq321286 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq321286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321286
  have eq336195 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq335942
  have eq336432 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq336195
       grind)
    | exact superpose eq336195 eq10
    | exact resolve eq10 eq336195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336195
  have eq336647 : x = y ∨ x = y := by
    first
    | (have i₁ := eq336432
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq336432
    | exact resolve eq336432 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336432
  have eq336648 : x = y := by grind
  clear eq336647
  have eq336657 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq336648
       grind)
    | exact superpose eq336648 eq16
    | exact resolve eq16 eq336648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336648
  have eq336658 : False := by grind
  exact eq336658

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_y_pyx_Equation723 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq92 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X3 (M.op X1 (M.op X2 (M.op (M.op X0 X1) X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op (M.op X0 X1) X1)) X3 X2
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 (M.op (M.op X0 X1) X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) X1) (M.op X2 (M.op (M.op X0 X1) X1)) X2
       have i₂ := eq9 X1 (M.op X2 (M.op (M.op X0 X1) X1)) X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq445 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq92 X0 X1 X1 X2
       have i₂ := eq9 X1 X1 X0
       grind)
    | exact superpose eq9 eq92
    | exact resolve eq92 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq468 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X0 X2)) = (M.op X3 (M.op X3 X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq445 x X2 X3
       have i₂ := eq445 x X2 X0
       grind)
    | exact superpose eq445 eq445
    | exact resolve eq445 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 X2 : G, (M.op X2 (M.op X0 (M.op X0 X2))) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X2 X2 x
       have i₂ := eq445 x X2 X0
       grind)
    | exact superpose eq445 eq9
    | exact resolve eq9 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq530 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq478 X0 (M.op X0 X0)
       have i₂ := eq478 X0 X0
       grind)
    | exact superpose eq478 eq478
    | exact resolve eq478 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93 X2 (M.op X0 (M.op X0 X2)) X2
       have i₂ := eq478 X0 X2
       grind)
    | exact superpose eq478 eq93
    | exact resolve eq93 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq538 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq535 X2 X0 X2
       have i₂ := eq478 X0 X2
       grind)
    | (have i₁ := eq535 X0 X1 X2
       have i₂ := eq478 X0 (M.op X0 (M.op X1 (M.op X1 X0)))
       grind)
    | exact superpose eq478 eq535
    | exact resolve eq535 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq548 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq530 X0
       grind)
    | exact superpose eq530 eq9
    | exact resolve eq9 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq619 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq468 X2 (M.op X1 (M.op X0 X0)) X1
       have i₂ := eq548 X0 X1
       grind)
    | exact superpose eq548 eq468
    | exact resolve eq468 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq899 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq538 (M.op X1 (M.op X0 X0)) X2 X1
       have i₂ := eq548 X0 X1
       grind)
    | exact superpose eq548 eq538
    | exact resolve eq538 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq945 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq899 X0 X1 x
       have i₂ := eq619 X0 X1 x
       grind)
    | exact superpose eq619 eq899
    | exact resolve eq899 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619 eq899
  have eq1223 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq548 X0 X1
       have i₂ := eq945 X0 X1
       grind)
    | (have i₁ := eq548 X0 X0
       have i₂ := eq945 X0 X0
       grind)
    | exact superpose eq945 eq548
    | exact resolve eq548 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq945
  have eq1309 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (M.op (σ X0) (M.op (σ X1) (σ X0)))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq478 (σ X0) (σ X1)
       have i₂ := eq303 X0 X1
       grind)
    | (have i₁ := eq478 (σ X1) (σ X0)
       have i₂ := eq303 X0 X1
       grind)
    | exact superpose eq303 eq478
    | (have j1 := eq303 X0 X1
       grind)
    | exact resolve eq478 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303 eq478
  have eq1324 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1309 X0 X1
       have i₂ := eq1223 (σ X0) (σ X1)
       grind)
    | exact superpose eq1223 eq1309
    | (have j0 := eq1309 X0 X1
       grind)
    | exact resolve eq1309 eq1223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223 eq1309
  have eq1325 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1324 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq23448 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1325 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1325
    | exact resolve eq1325 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23478 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1325 y x
       grind)
    | exact superpose eq1325 eq16
    | (have j1 := eq1325 x y
       grind)
    | exact resolve eq16 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325
  have eq23556 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23448 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq23448
    | (have j0 := eq23448 X0 X1
       grind)
    | exact resolve eq23448 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq23448
  have eq23562 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23556 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23556
    | exact resolve eq23556 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23556
  have eq23650 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq23478
       have i₂ := eq23562 x y
       grind)
    | exact superpose eq23562 eq23478
    | (have j1 := eq23562 (σ x) (σ y)
       grind)
    | (have r₁ := eq23478
       have r₂ := eq23562 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq23478
       have r₂ := eq23562 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq23478 eq23562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23478 eq23562
  have eq23653 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq23650
  have eq23655 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq23653
       grind)
    | exact superpose eq23653 eq10
    | exact resolve eq10 eq23653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23653
  have eq23729 : x = y ∨ x = y := by
    first
    | (have i₁ := eq23655
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23655
    | exact resolve eq23655 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23655
  have eq23730 : x = y := by grind
  clear eq23729
  have eq23735 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23730
       grind)
    | exact superpose eq23730 eq16
    | exact resolve eq16 eq23730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23730
  have eq23736 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq23735
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq23735
    | (have r₁ := eq23735
       have r₂ := eq22 x
       grind)
    | exact resolve eq23735 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq23735
  have eq23737 : False := by grind
  exact eq23737

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation723 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq103 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
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
  have eq104 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
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
  have eq417 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq434 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq417 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq417
    | (have j0 := eq417 X0 X1
       grind)
    | exact resolve eq417 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq589 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq103 X0 X2 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq103
    | exact resolve eq103 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq610 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq589 X1 x X3
       have i₂ := eq589 X1 x X0
       grind)
    | exact superpose eq589 eq589
    | exact resolve eq589 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq622 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 x
       have i₂ := eq589 X1 x X0
       grind)
    | exact superpose eq589 eq9
    | exact resolve eq9 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq634 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104 X0 (M.op X2 X0) X2
       have i₂ := eq589 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq589 eq104
    | exact resolve eq104 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq646 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq634 X0 X1 X2
       have i₂ := eq104 X0 X0 X1
       grind)
    | exact superpose eq104 eq634
    | exact resolve eq634 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq667 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq622 X0 (M.op X0 X0)
       have i₂ := eq622 X0 X0
       grind)
    | exact superpose eq622 eq622
    | exact resolve eq622 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq667 X0
       grind)
    | exact superpose eq667 eq9
    | exact resolve eq9 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq686 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq686
    | exact resolve eq686 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq733 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq610 X0 (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq622 X1 X0
       grind)
    | exact superpose eq622 eq610
    | exact resolve eq610 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq735 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X2 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq610 X2 (M.op X2 X1) X3
       have i₂ := eq610 X2 X1 X0
       grind)
    | (have i₁ := eq610 X2 (M.op X2 X1) X3
       have i₂ := eq610 X0 X1 X2
       grind)
    | exact superpose eq610 eq610
    | exact resolve eq610 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq861 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq646 X0 X1 X0
       have i₂ := eq667 X0
       grind)
    | exact superpose eq667 eq646
    | exact resolve eq646 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646 eq667
  have eq937 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 X1 X1
       have i₂ := eq861 X0 X1
       grind)
    | exact superpose eq861 eq104
    | exact resolve eq104 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq861
  have eq968 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq937 X1 X1
       have i₂ := eq610 X1 X1 X0
       grind)
    | (have i₁ := eq937 X1 X1
       have i₂ := eq610 X0 X1 X1
       grind)
    | exact superpose eq610 eq937
    | exact resolve eq937 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq1076 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq622 (M.op X1 (M.op X1 X0)) X0
       have i₂ := eq968 X1 X0
       grind)
    | exact superpose eq968 eq622
    | exact resolve eq622 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq1330 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq733 (M.op X1 X0) X1 X1
       have i₂ := eq733 X0 X1 X1
       grind)
    | exact superpose eq733 eq733
    | exact resolve eq733 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1333 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq733 X2 X1 X1
       have i₂ := eq610 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq733 X2 X1 X1
       have i₂ := eq610 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq610 eq733
    | exact resolve eq733 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq2452 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1333 X2 X0 (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0))
       have i₂ := eq1076 X0 X1
       grind)
    | exact superpose eq1076 eq1333
    | exact resolve eq1333 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq2615 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2452 X0 X1 X2
       have i₂ := eq1330 (M.op X0 X0) (M.op X1 (M.op X1 X0))
       grind)
    | exact superpose eq1330 eq2452
    | exact resolve eq2452 eq1330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2452
  have eq2655 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op X1 (M.op X1 X0)) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2615 X0 X1 X2
       have i₂ := eq1330 X0 X0
       grind)
    | exact superpose eq1330 eq2615
    | exact resolve eq2615 eq1330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330 eq2615
  have eq2687 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2655 X0 X1 x
       have i₂ := eq622 x X0
       grind)
    | exact superpose eq622 eq2655
    | exact resolve eq2655 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2655
  have eq3129 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq434 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq434
    | (have j0 := eq434 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | exact resolve eq434 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq3645 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X2 X1)) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2687 X1 X2
       have i₂ := eq610 X1 X1 X0
       grind)
    | (have i₁ := eq2687 X1 X2
       have i₂ := eq610 X0 X1 X1
       grind)
    | exact superpose eq610 eq2687
    | exact resolve eq2687 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610 eq2687
  have eq30635 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X3 X2)) (M.op X3 (M.op X3 X2))) = (M.op X1 (M.op X4 (M.op X4 (M.op X0 (M.op X0 (M.op X1 X2)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1333 X4 X1 (M.op X3 (M.op X3 X2))
       have i₂ := eq735 X3 X2 X1 X0
       grind)
    | (have i₁ := eq1333 X0 X3 (M.op X3 (M.op X2 X1))
       have i₂ := eq735 X0 X1 X2 X3
       grind)
    | exact superpose eq735 eq1333
    | exact resolve eq1333 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq1333
  have eq30736 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X4 (M.op X4 (M.op X0 (M.op X0 (M.op X1 X2)))))) = X2 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq30635 X0 X1 X2 x X4
       have i₂ := eq3645 x X2 x
       grind)
    | exact superpose eq3645 eq30635
    | exact resolve eq30635 eq3645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3645 eq30635
  have eq71737 : ∀ X0 X1 X2 X3 : G, (σ X3) = (M.op (σ X0) (M.op X1 (M.op X1 (M.op X2 (M.op X2 (σ (M.op X0 X0))))))) ∨ (σ (M.op X0 X3)) = (M.op (σ X0) (σ X3)) ∨ (σ X0) = (σ X3) ∨ (M.op X0 X0) = (M.op X0 X3) ∨ X0 = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30736 X2 (σ X0) (σ X3) X1
       have i₂ := eq3129 X0 X3
       grind)
    | exact superpose eq3129 eq30736
    | (have j1 := eq3129 X0 X3
       grind)
    | exact resolve eq30736 eq3129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3129
  have eq71767 : ∀ X0 X1 X3 : G, (σ X3) = (M.op (σ X0) (M.op X1 (M.op X1 (σ X0)))) ∨ (σ (M.op X0 X3)) = (M.op (σ X0) (σ X3)) ∨ (σ X0) = (σ X3) ∨ (M.op X0 X0) = (M.op X0 X3) ∨ X0 = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq71737 X0 X1 x X3
       have i₂ := eq702 X0 x
       grind)
    | exact superpose eq702 eq71737
    | (have j0 := eq71737 X0 X1 x X3
       grind)
    | exact resolve eq71737 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq71737
  have eq71900 : ∀ X0 X3 : G, (σ X0) = (σ X3) ∨ (σ (M.op X0 X3)) = (M.op (σ X0) (σ X3)) ∨ (σ X0) = (σ X3) ∨ (M.op X0 X0) = (M.op X0 X3) ∨ X0 = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq71767 X0 x X3
       have i₂ := eq622 x (σ X0)
       grind)
    | exact superpose eq622 eq71767
    | (have j0 := eq71767 X0 x X3
       grind)
    | exact resolve eq71767 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622 eq71767
  have eq71901 : ∀ X0 X3 : G, (σ X0) = (σ X3) ∨ (σ (M.op X0 X3)) = (M.op (σ X0) (σ X3)) ∨ (M.op X0 X0) = (M.op X0 X3) ∨ X0 = X3 := by
    intro X0 X3
    first
    | (have j0 := eq71900 X0 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71900
  have eq72005 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq71901 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71901
  have eq323342 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq72005 x y
       grind)
    | exact superpose eq72005 eq16
    | (have j1 := eq72005 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq72005 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq72005 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq72005 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq72005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72005
  have eq323592 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq323342
  have eq323986 : ∀ X0 X1 : G, y = (M.op x (M.op X0 (M.op X0 (M.op X1 (M.op X1 (M.op x x)))))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq30736 X1 x y X0
       have i₂ := eq323592
       grind)
    | exact superpose eq323592 eq30736
    | exact resolve eq30736 eq323592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323592
  have eq324087 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq323986 x x
       have i₂ := eq30736 x x x x
       grind)
    | exact superpose eq30736 eq323986
    | exact resolve eq323986 eq30736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30736 eq323986
  have eq324088 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq324087
  have eq324143 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq324088
  have eq324207 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq324143
       grind)
    | exact superpose eq324143 eq10
    | exact resolve eq10 eq324143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324143
  have eq324409 : x = y ∨ x = y := by
    first
    | (have i₁ := eq324207
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq324207
    | exact resolve eq324207 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324207
  have eq324410 : x = y := by grind
  clear eq324409
  have eq324419 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq324410
       grind)
    | exact superpose eq324410 eq16
    | exact resolve eq16 eq324410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324410
  have eq324420 : False := by grind
  exact eq324420

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation723 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq28 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq39 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq81 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq28
    | (have j0 := eq28 X0 X1
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq39 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq39
    | exact resolve eq39 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq431 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq415 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq415
    | (have j0 := eq415 X0 X1
       grind)
    | exact resolve eq415 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq996 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq81 x y
       grind)
    | exact superpose eq81 eq16
    | (have j1 := eq81 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq81 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq81 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq81 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq1019 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq996
  have eq1996 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1019
       grind)
    | exact superpose eq1019 eq16
    | exact resolve eq16 eq1019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1998 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq1019
       grind)
    | exact superpose eq1019 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1019
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1019
       grind)
    | exact resolve eq13 eq1019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq2015 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1998
  have eq2016 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq2015
  have eq2030 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2016
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2016
    | exact resolve eq2016 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2016
  have eq4695 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq431 x y
       have i₂ := eq2030
       grind)
    | exact superpose eq2030 eq431
    | (have j0 := eq431 x y
       grind)
    | exact resolve eq431 eq2030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq4697 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq2030
       grind)
    | exact superpose eq2030 eq10
    | exact resolve eq10 eq2030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2030
  have eq4724 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq4695
  have eq4735 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4697
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq4697
    | exact resolve eq4697 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4697
  have eq4736 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq4724
       have r₂ := eq1996
       grind)
    | exact resolve eq4724 eq1996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1996 eq4724
  have eq4741 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 y (k y x)
       grind)
    | (have r₁ := eq4735
       have r₂ := eq13 y x
       grind)
    | exact resolve eq4735 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4735
  have eq11918 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq4741
       grind)
    | exact superpose eq4741 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq4741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4741
  have eq11921 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11918
  have eq55101 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq11921
       grind)
    | exact superpose eq11921 eq16
    | exact resolve eq16 eq11921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11921
  have eq73605 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq55101
       have i₂ := eq4736
       grind)
    | exact superpose eq4736 eq55101
    | exact resolve eq55101 eq4736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4736 eq55101
  have eq73606 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq73605
  have eq73607 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq73606
  have eq87728 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq73607
       grind)
    | exact superpose eq73607 eq10
    | exact resolve eq10 eq73607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73607
  have eq87910 : x = y ∨ x = y := by
    first
    | (have i₁ := eq87728
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq87728
    | exact resolve eq87728 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87728
  have eq87911 : x = y := by grind
  clear eq87910
  have eq110471 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq87911
       grind)
    | exact superpose eq87911 eq16
    | exact resolve eq16 eq87911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87911
  have eq110472 : False := by grind
  exact eq110472
